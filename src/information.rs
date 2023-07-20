use core::alloc::Layout;
use core::cell::Cell;
use alloc::boxed::Box;
use alloc::vec::Vec;
use alloc::slice;
use alloc::{collections::BTreeMap, alloc::dealloc};
use alloc::alloc::alloc;

use multiboot::information::{
    ColorInfoRgb,
    ColorInfoType,
    ElfSymbols,
    FramebufferTable,
    MemoryManagement,
    Multiboot,
    MultibootInfo,
    MemoryEntry as MultibootMemoryEntry,
    MemoryType as MultibootMemoryType,
    Module as MultibootModule,
    PAddr,
    SymbolType,
    SIGNATURE_EAX as MULTIBOOT_EAX_SIGNATURE,
};
use multiboot2::{
    BasicMemoryInfoTag,
    BootInformation as Multiboot2BootInformation,
    BootInformationHeader as Multiboot2BootInformationHeader,
    BootLoaderNameTag,
    CommandLineTag,
    EFIImageHandle32Tag, EFIImageHandle64Tag, EFIMemoryMapTag,
    EFISdt32Tag, EFISdt64Tag,
    ElfSectionsTag,
    FramebufferField,
    FramebufferTag,
    FramebufferType,
    ImageLoadPhysAddrTag,
    MemoryArea,
    MemoryAreaType,
    MemoryMapTag,
    ModuleTag,
    MAGIC as MULTIBOOT2_EAX_SIGNATURE,
    RsdpV1Tag, RsdpV2Tag, SmbiosTag,
};
pub use multiboot2::EFIMemoryDesc as EfiMemoryDescriptor;
use multiboot2::builder::{BoxedDst, InformationBuilder as Multiboot2InformationBuilder};
use ouroboros::self_referencing;

pub type MemoryUpdateFunction = Box<dyn FnMut(&mut [u8], u32, u32, &[MemoryEntry], Option<&[EfiMemoryDescriptor]>)>;

pub enum InfoBuilder {
    Multiboot(MultibootInfoBuilder),
    Multiboot2(UpdateCell<Multiboot2InformationBuilder>),
}

impl InfoBuilder {
    pub(crate) fn new_multiboot() -> Self {
        Self::Multiboot(MultibootInfoBuilder::new(
            MultibootInfo::default(), MultibootAllocator::new(),
            Vec::new(), |i, a| Multiboot::from_ref(i, a),
        ))
    }

    pub(crate) fn new_multiboot2() -> Self {
        Self::Multiboot2(UpdateCell::new(Multiboot2InformationBuilder::new()))
    }

    /// Note: This allocates.
    /// Also, since the return value contains a Box, dropping it deallocates.
    pub fn build(self) -> (Vec<u8>, u32, MemoryUpdateFunction) {
        match self {
            Self::Multiboot(bu) => {
                let mut heads = bu.into_heads();
                (
                    unsafe { core::slice::from_raw_parts(
                        &heads.info as *const MultibootInfo as *const u8,
                        core::mem::size_of::<MultibootInfo>(),
                    ) }.to_vec(),
                    MULTIBOOT_EAX_SIGNATURE,
                    Box::new(move |info_bytes: &mut [u8], lower: u32, upper: u32, entries: &[MemoryEntry], _efi_mmap: Option<&[EfiMemoryDescriptor]>| {
                        let (_head, body, _tail) = unsafe {
                            info_bytes.align_to_mut::<MultibootInfo>()
                        };
                        let mut info = &mut body[0];
                        let mut multiboot = Multiboot::from_ref(
                            &mut info, &mut heads.allocator,
                        );
                        multiboot.set_memory_bounds(Some((lower, upper)));
                        MultibootInfoBuilder::copy_memory_regions(
                            &mut heads.memory_map_vec, entries,
                        );
                    }),
                )
            },
            Self::Multiboot2(c) => {
                (
                    c.into_inner().build().to_vec(), MULTIBOOT2_EAX_SIGNATURE,
                    Box::new(|info_bytes: &mut [u8], lower: u32, upper: u32, entries: &[MemoryEntry], efi_mmap: Option<&[EfiMemoryDescriptor]>| {
                        let mut info = unsafe {
                            Multiboot2BootInformation::load_mut(info_bytes.as_mut_ptr() as *mut Multiboot2BootInformationHeader)
                        }.unwrap();
                        let mem_map_tag = info.memory_map_tag_mut().unwrap();
                        entries.into_iter().zip(
                            mem_map_tag.all_memory_areas_mut()
                        ).for_each(
                            |(source, destination)| match source {
                                MemoryEntry::Multiboot(_)
                                    => panic!("wrong Multiboot version"),
                                MemoryEntry::Multiboot2(src)
                                    => *destination = src.clone(),
                            }
                        );
                        let mut info = unsafe {
                            Multiboot2BootInformation::load_mut(info_bytes.as_mut_ptr() as *mut Multiboot2BootInformationHeader)
                        }.unwrap();
                        let mem_info_tag = info.basic_memory_info_tag_mut().unwrap();
                        *mem_info_tag = BasicMemoryInfoTag::new(lower, upper);
                        let mut info = unsafe {
                            Multiboot2BootInformation::load_mut(info_bytes.as_mut_ptr() as *mut Multiboot2BootInformationHeader)
                        }.unwrap();
                        if let Some(mmap) = efi_mmap {
                            let efi_mmap_tag = info.efi_memory_map_tag_mut().unwrap();
                            mmap.into_iter().zip(
                                efi_mmap_tag.memory_areas_mut()
                            ).for_each(|(src, dest)| *dest = src.clone() );
                        }
                    }),
                )
            },
        }
    }

    pub fn new_color_info_rgb(&self,
        red_field_position: u8,
        red_mask_size: u8,
        green_field_position: u8,
        green_mask_size: u8,
        blue_field_position: u8,
        blue_mask_size: u8,
    ) -> ColorInfo {
        match self {
            Self::Multiboot(_) => ColorInfo::Multiboot(ColorInfoType::Rgb(ColorInfoRgb {
                red_field_position,
                red_mask_size,
                green_field_position,
                green_mask_size,
                blue_field_position,
                blue_mask_size,
            })),
            Self::Multiboot2(_) => ColorInfo::Multiboot2(FramebufferType::RGB {
                red: FramebufferField {
                    position: red_field_position,
                    size: red_mask_size,
                },
                green: FramebufferField {
                    position: green_field_position,
                    size: green_mask_size,
                },
                blue: FramebufferField {
                    position: blue_field_position,
                    size: blue_mask_size,
                },
            }),
        }
    }

    pub fn new_memory_entry(&self, base_addr: u64, length: u64, ty: MemoryType, ) -> MemoryEntry {
        match self {
            Self::Multiboot(_) => MemoryEntry::Multiboot(
                MultibootMemoryEntry::new(base_addr, length, ty.to_multiboot())
            ),
            Self::Multiboot2(_) => MemoryEntry::Multiboot2(
                MemoryArea::new(base_addr, length, ty.to_multiboot2())
            ),
        }
    }

    pub fn allocate_memory_map_vec(&mut self, count: usize) -> Vec<MemoryEntry> {
        match self {
            Self::Multiboot(b) => b.allocate_memory_map_vec(count),
            Self::Multiboot2(c) => {
                // allocate empty memory entries
                let mut v = Vec::new();
                v.resize_with(count, || MemoryArea::new(0, 0, MemoryAreaType::Reserved));
                c.update(|b| b.memory_map_tag(MemoryMapTag::new(v.as_slice())))
            },
        }
        let mut v = Vec::new();
        v.resize_with(
            count, || self.new_memory_entry(0, 0, MemoryType::Reserved),
        );
        v
    }

    pub fn allocate_efi_memory_map_vec(&mut self, count: usize) -> Vec<EfiMemoryDescriptor> {
        match self {
            // Multiboot1 doesn't support passing EFI memory maps.
            Self::Multiboot(_) => (),
            Self::Multiboot2(c) => {
                // allocate empty memory entries
                let mut v = Vec::new();
                v.resize(count, EfiMemoryDescriptor::default());
                c.update(|b| b.efi_memory_map_tag(EFIMemoryMapTag::new(v.as_slice())))
            },
        }
        let mut v = Vec::new();
        v.resize(count, EfiMemoryDescriptor::default());
        v
    }

    pub fn new_module<'a>(&self, start: u32, end: u32, cmdline: Option<&'a str>) -> Module<'a> {
        match self {
            Self::Multiboot(_) => Module::Multiboot(MultibootModule::new(
                start.into(), end.into(), cmdline,
            )),
            Self::Multiboot2(_) => Module::Multiboot2(ModuleTag::new(
                start, end, cmdline.unwrap_or(""),
            )),
        }
    }

     pub fn set_boot_loader_name(&mut self, name: Option<&str>) {
        match self {
            Self::Multiboot(b) => b.with_wrap_mut(|w| w.set_boot_loader_name(name)),
            Self::Multiboot2(c) => if let Some(n) = name {
                c.update(|b| b.bootloader_name_tag(BootLoaderNameTag::new(n)))
            },
        }
    }

    pub fn set_boot_services_not_exited(&mut self) {
        match self {
            // Multiboot1 doesn't know this.
            Self::Multiboot(_) => (),
            Self::Multiboot2(c) => c.update(|b| b.efi_boot_services_not_exited_tag())
        }
    }

    pub fn set_command_line(&mut self, cmdline: Option<&str>) {
        match self {
            Self::Multiboot(b) => b.with_wrap_mut(|w| w.set_command_line(cmdline)),
            Self::Multiboot2(cell) => if let Some(cmd) = cmdline {
                cell.update(|b| b.command_line_tag(CommandLineTag::new(cmd)))
            },
        }
    }

    pub fn set_efi_image_handle32(&mut self, pointer: u32) {
        match self {
            Self::Multiboot(_) => (), // Multiboot1 doesn't know about this
            Self::Multiboot2(c) => c.update(|b| b.efi_image_handle32(
                EFIImageHandle32Tag::new(pointer)
            )),
        }
    }

    pub fn set_efi_image_handle64(&mut self, pointer: u64) {
        match self {
            Self::Multiboot(_) => (), // Multiboot1 doesn't know about this
            Self::Multiboot2(c) => c.update(|b| b.efi_image_handle64(
                EFIImageHandle64Tag::new(pointer)
            )),
        }
    }

    pub fn set_memory_bounds(&mut self, bounds: Option<(u32, u32)>) {
        match self {
            Self::Multiboot(i) => i.with_wrap_mut(
                |w| w.set_memory_bounds(bounds)
            ),
            Self::Multiboot2(c) => if let Some((lower, upper)) = bounds {
                c.update(|b| b.basic_memory_info_tag(BasicMemoryInfoTag::new(lower, upper)))
            },
        }
    }

    pub fn set_framebuffer_table(&mut self, table: Option<FramebufferInfo>) {
        match self {
            Self::Multiboot(b) => b.with_wrap_mut(|w| w.set_framebuffer_table(
                table.map(|t| match t {
                    FramebufferInfo::Multiboot(i) => i,
                    FramebufferInfo::Multiboot2(_) => panic!("wrong Multiboot version"),
                })
            )),
            Self::Multiboot2(c) => if let Some(tab) = table {
                match tab {
                    FramebufferInfo::Multiboot(_) => panic!("wrong Multiboot version"),
                    FramebufferInfo::Multiboot2(t) => c.update(|b| b.framebuffer_tag(t)),
                }
            },
        }
    }

    pub fn set_image_load_addr(&mut self, addr: u32) {
        match self {
            Self::Multiboot(_) => (), // Multiboot1 doesn't know this
            Self::Multiboot2(c) => c.update(|b| b.image_load_addr(ImageLoadPhysAddrTag::new(addr))),
        }
    }

    pub fn set_memory_regions(&mut self, regions: Option<&[MemoryEntry]>) {
        match self {
            Self::Multiboot(b) => b.set_memory_regions(regions),
            Self::Multiboot2(c) => if let Some(regs) = regions {
                    let v: Vec<_> = regs.iter().map(|me| match me {
                        MemoryEntry::Multiboot(_) => panic!("wrong Multiboot version"),
                        MemoryEntry::Multiboot2(ma) => ma.clone(),
                    }).collect();
                    c.update(|b| b.memory_map_tag(MemoryMapTag::new(v.as_slice())))
            },
        }
    }

    pub fn set_modules(&mut self, modules: Option<Vec<Module>>) {
        match self {
            Self::Multiboot(b) => b.with_wrap_mut(|w| 
                match modules {
                    None => w.set_modules(None),
                    Some(mods) => {
                        let v: Vec<_> = mods.into_iter().map(|mo|match mo {
                            Module::Multiboot(m) => m,
                            Module::Multiboot2(_) => panic!("wrong Multiboot version"),
                        }).collect();
                        w.set_modules(Some(v.as_slice()))
                    }
                }
            ),
            Self::Multiboot2(c) => if let Some(mods) = modules {
                for mo in mods {
                    match mo {
                        Module::Multiboot(_) => panic!("wrong Multiboot version"),
                        Module::Multiboot2(m) => c.update(|b| b.add_module_tag(m)),
                    }
                }
            },
        }
    }

    pub fn set_rsdp_v1(
        &mut self, signature: [u8; 8], checksum: u8, oem_id: [u8; 6],
        revision: u8, rsdt_address: u32,
    ) {
        match self {
            Self::Multiboot(_) => (), // not supported on Multiboot1
            Self::Multiboot2(c) => c.update(|b| b.rsdp_v1_tag(RsdpV1Tag::new(
                signature, checksum, oem_id, revision, rsdt_address,
            ))),
        }
    }

    pub fn set_rsdp_v2(
        &mut self, signature: [u8; 8], checksum: u8, oem_id: [u8; 6],
        revision: u8, rsdt_address: u32, length: u32, xsdt_address: u64,
        ext_checksum: u8,
    ) {
        match self {
            Self::Multiboot(_) => (), // not supported on Multiboot1
            Self::Multiboot2(c) => c.update(|b| b.rsdp_v2_tag(RsdpV2Tag::new(
                signature, checksum, oem_id, revision, rsdt_address, length,
                xsdt_address, ext_checksum,
            ))),
        }
    }

    pub fn add_smbios_tag(&mut self, major: u8, minor: u8, tables: &[u8]) {
        match self {
            Self::Multiboot(_) => (), // not suppported on Multiboot1
            Self::Multiboot2(c) => c.update(|b| b.add_smbios_tag(
                SmbiosTag::new(major, minor, tables)
            )),
        }
    }

    pub fn set_symbols(&mut self, symbols: Option<Symbols>) {
        match self {
            Self::Multiboot(b) => {
                b.with_wrap_mut(|w| w.set_symbols(symbols.map(|s| match s {
                    Symbols::Multiboot(t) => t,
                    Symbols::Multiboot2(_) => panic!("wrong Multiboot version"),
                })))
            },
            Self::Multiboot2(c) => if let Some(syms) = symbols {
                match syms {
                    Symbols::Multiboot(_) => panic!("wrong Multiboot version"),
                    Symbols::Multiboot2(sy) => if let Some(s) = sy {
                        c.update(|b| b.elf_sections_tag(s))
                    }
                }
            },
        }
    }

    pub fn set_system_table_ia32(&mut self, systab: Option<u32>) {
        match self {
            Self::Multiboot(_) => (), // not suppported on Multiboot1
            Self::Multiboot2(c) => if let Some(st) = systab {
                c.update(|b| b.efisdt32_tag(EFISdt32Tag::new(st)))
            },
        }
    }

    pub fn set_system_table_x64(&mut self, systab: Option<u64>) {
        match self {
            Self::Multiboot(_) => (), // not suppported on Multiboot1
            Self::Multiboot2(c) => if let Some(st) = systab {
                c.update(|b| b.efisdt64_tag(EFISdt64Tag::new(st)))
            },
        }
    }
}

#[self_referencing]
pub struct MultibootInfoBuilder {
    info: MultibootInfo,
    allocator: MultibootAllocator,
    memory_map_vec: Vec<MultibootMemoryEntry>,
    #[borrows(mut info, mut allocator)]
    #[not_covariant]
    wrap: Multiboot<'this, 'this>,
}

impl MultibootInfoBuilder {
    fn allocate_memory_map_vec(&mut self, count: usize) {
        self.with_mut(|f| {
            f.memory_map_vec.resize(count, MultibootMemoryEntry::default());
            f.wrap.set_memory_regions(Some((f.memory_map_vec.as_slice().as_ptr() as PAddr, count)));
        })
    }

    fn set_memory_regions(&mut self, regions: Option<&[MemoryEntry]>) {
        self.with_mut(|s|
            match regions {
                None => s.wrap.set_memory_regions(None),
                Some(regs) => {
                    Self::copy_memory_regions(s.memory_map_vec, regs);
                    s.wrap.set_memory_regions(Some(
                        (s.memory_map_vec.as_slice().as_ptr() as PAddr, regs.len())
                    ))
                }
            }
        )
    }

    /// Write the entries into the vec.
    fn copy_memory_regions(memory_map_vec: &mut Vec<MultibootMemoryEntry>, regions: &[MemoryEntry]) {
        memory_map_vec.truncate(regions.len());
        regions.into_iter().zip(memory_map_vec.iter_mut()).for_each(
            |(source, destination)| match source {
                MemoryEntry::Multiboot(src) => *destination = *src,
                MemoryEntry::Multiboot2(_) => panic!("wrong Multiboot version"),
            }
        );
    }
}

/// Proxy Rust's allocator to the multiboot crate.
pub(super) struct MultibootAllocator {
    allocations: BTreeMap<u64, Layout>
}

impl MultibootAllocator {
    /// Initialize the allocator.
    pub(super) fn new() -> Self {
        MultibootAllocator { allocations: BTreeMap::new() }
    }
}

impl MemoryManagement for MultibootAllocator {
    /// Get a slice to the memory referenced by the pointer.
    unsafe fn paddr_to_slice(
        &self, addr: u64, _length: usize
    ) -> Option<&'static [u8]> {
        // Using layout.size instead of length brings us safety, but may be too strict.
        self.allocations.get(&addr).map(|layout|
            core::slice::from_raw_parts(addr as *const u8, layout.size())
        )
    }

    /// Allocate n bytes of memory and return the address.
    unsafe fn allocate(
        &mut self, length: usize
    ) -> Option<(u64, &mut [u8])> {
        let layout = Layout::array::<u8>(length).expect("tried to allocate more than usize");
        let ptr = alloc(layout);
        if ptr as usize >= u32::MAX as usize {
            return None
        }
        if ptr.is_null() {
            None
        } else {
            self.allocations.insert(ptr as u64, layout);
            Some((
                ptr as u64,
                core::slice::from_raw_parts_mut(ptr, length),
            ))
        }
    }
    
    /// Free the previously allocated memory.
    unsafe fn deallocate(&mut self, addr: u64) {
        if addr == 0 {
            return;
        }
        match self.allocations.remove(&addr) {
            None => panic!(
                "couldn't free memory that has not been previously allocated: {addr}"
            ),
            Some(layout) => dealloc(addr as *mut u8, layout)
        }
    }
}

// TODO: Check whether the Clone breaks anything?
#[derive(Debug, Clone)]
pub enum MemoryEntry {
    Multiboot(MultibootMemoryEntry),
    Multiboot2(MemoryArea),
}

impl MemoryEntry {
    pub fn with(&self, base_addr: u64, length: u64, ty: MemoryType) -> Self {
        match self {
            Self::Multiboot(_) => MemoryEntry::Multiboot(
                MultibootMemoryEntry::new(base_addr, length, ty.to_multiboot())
            ),
            Self::Multiboot2(_) => MemoryEntry::Multiboot2(
                MemoryArea::new(base_addr, length, ty.to_multiboot2())
            ),
        }
    }

    pub fn base_address(&self) -> u64 {
        match self {
            Self::Multiboot(e) => e.base_address(),
            Self::Multiboot2(a) => a.start_address(),
        }
    }

    pub fn length(&self) -> u64 {
        match self {
            Self::Multiboot(e) => e.length(),
            Self::Multiboot2(a) => a.size(),
        }
    }

    pub fn memory_type(&self) -> MemoryType {
        match self {
            Self::Multiboot(e) => match e.memory_type() {
                MultibootMemoryType::Available => MemoryType::Available,
                MultibootMemoryType::Reserved => MemoryType::Reserved,
                MultibootMemoryType::ACPI => MemoryType::AcpiAvailable,
                MultibootMemoryType::NVS => MemoryType::ReservedHibernate,
                MultibootMemoryType::Defect => MemoryType::Defective,
            },
            Self::Multiboot2(a) => match a.typ().into() {
                MemoryAreaType::Available => MemoryType::Available,
                MemoryAreaType::Reserved => MemoryType::Reserved,
                MemoryAreaType::AcpiAvailable => MemoryType::AcpiAvailable,
                MemoryAreaType::ReservedHibernate => MemoryType::ReservedHibernate,
                MemoryAreaType::Defective => MemoryType::Defective,
                MemoryAreaType::Custom(_) => MemoryType::Reserved, // just to be sure
            },
        }
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum MemoryType {
    Available,
    Reserved,
    AcpiAvailable,
    ReservedHibernate,
    Defective,
}

impl MemoryType {
    // TODO: this could be an into
    fn to_multiboot(&self) -> MultibootMemoryType {
        match self {
            MemoryType::Available => MultibootMemoryType::Available,
            MemoryType::Reserved => MultibootMemoryType::Reserved,
            MemoryType::AcpiAvailable => MultibootMemoryType::ACPI,
            MemoryType::ReservedHibernate => MultibootMemoryType::NVS,
            MemoryType::Defective => MultibootMemoryType::Defect,
        }
    }

    fn to_multiboot2(&self) -> MemoryAreaType {
        match self {
            MemoryType::Available => MemoryAreaType::Available,
            MemoryType::Reserved => MemoryAreaType::Reserved,
            MemoryType::AcpiAvailable => MemoryAreaType::AcpiAvailable,
            MemoryType::ReservedHibernate => MemoryAreaType::ReservedHibernate,
            MemoryType::Defective => MemoryAreaType::Defective,
        }
    }
}

pub enum Module<'a> {
    Multiboot(MultibootModule<'a>),
    Multiboot2(BoxedDst<ModuleTag>),
}

pub enum Symbols {
    Multiboot(SymbolType),
    Multiboot2(Option<BoxedDst<ElfSectionsTag>>),
}

impl Symbols {
    pub(crate) fn new_multiboot(
        num: u32, size: u32, addr: usize, shndx: u32
    ) -> Self {
        Self::Multiboot(SymbolType::Elf(
            ElfSymbols::from_addr(
                num, size, addr.try_into().unwrap(), shndx,
            )
        ))
    }

    pub(crate) fn new_multiboot2(
        num: u32, size: u32, addr: usize, shndx: u32
    ) -> Self {
        let bytes = unsafe { slice::from_raw_parts(
            addr as *mut u8, (num * size).try_into().unwrap()
        ) };
        Self::Multiboot2(Some(ElfSectionsTag::new(
            num, size, shndx, bytes,
        )))
    }
}

pub enum ColorInfo {
    Multiboot(ColorInfoType),
    Multiboot2(FramebufferType<'static>),
}

impl ColorInfo {
    pub fn to_framebuffer_info(self,
        addr: u64,
        pitch: u32,
        width: u32,
        height: u32,
        bpp: u8,
    ) -> FramebufferInfo {
        match self {
            Self::Multiboot(c) => FramebufferInfo::Multiboot(
                FramebufferTable::new(addr, pitch, width, height, bpp, c)
            ),
            Self::Multiboot2(t) => FramebufferInfo::Multiboot2(
                FramebufferTag::new(addr, pitch, width, height, bpp, t)
            ),
        }
    }
}

#[derive(Debug)]
pub enum FramebufferInfo {
    Multiboot(FramebufferTable),
    Multiboot2(BoxedDst<FramebufferTag>),
}


pub struct UpdateCell<T> {
    value: Cell<Option<T>>
}

impl<T> UpdateCell<T> {
    fn new(val: T) -> Self {
        Self { value: Cell::new(Some(val)) }
    }
    
    fn update<F: FnOnce(T) -> T>(&mut self, func: F) {
        let val = self.value.take().unwrap();
        self.value.set(Some(func(val)))
    }

    fn into_inner(self) -> T {
        self.value.take().unwrap()
    }
}
