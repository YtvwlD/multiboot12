use core::alloc::Layout;
use alloc::vec::Vec;
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
    SymbolType,
    SIGNATURE_EAX as MULTIBOOT_EAX_SIGNATURE,
};
use multiboot2::{
    ElfSectionsTag,
    FramebufferTag,
    FramebufferType,
    BootInformation,
    MemoryArea,
    MemoryAreaType,
    ModuleTag,
    MULTIBOOT2_BOOTLOADER_MAGIC as MULTIBOOT2_EAX_SIGNATURE,
};
use ouroboros::self_referencing;

pub enum InfoBuilder {
    Multiboot(MultibootInfoBuilder),
    Multiboot2(BootInformation),
}

impl InfoBuilder {
    pub(crate) fn new_multiboot() -> Self {
        Self::Multiboot(MultibootInfoBuilder::new(
            MultibootInfo::default(), MultibootAllocator::new(),
            |i, a| Multiboot::from_ref(i, a)
        ))
    }

    pub(crate) fn new_multiboot2() -> Self {
        Self::Multiboot2(todo!())
    }

    pub fn build(self) -> (MultibootInfo, u32) {
        match self {
            // TODO: Does this drop allocator?
            Self::Multiboot(bu) => (
                bu.into_heads().info, MULTIBOOT_EAX_SIGNATURE,
            ),
            Self::Multiboot2(_) => todo!(),
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
            Self::Multiboot2(_) => todo!(),
        }
    }

    pub fn new_memory_entry(&self, base_addr: u64, length: u64, ty: MemoryType, ) -> MemoryEntry {
        match self {
            Self::Multiboot(_) => MemoryEntry::Multiboot(
                MultibootMemoryEntry::new(base_addr, length, ty.to_multiboot())
            ),
            Self::Multiboot2(_) => MemoryEntry::Multiboot2(
                //MemoryArea::new(base_addr, length, ty.to_multiboot2())
                todo!()
            ),
        }
    }

    pub fn allocate_memory_info_vec(&self, count: usize) -> Vec<MemoryEntry> {
        let mut v = Vec::new();
        v.resize_with(
            count, || self.new_memory_entry(0, 0, MemoryType::Reserved),
        );
        v
    }

    pub fn new_module<'a>(&self, start: u64, end: u64, name: Option<&'a str>) -> Module<'a> {
        match self {
            Self::Multiboot(_) => Module::Multiboot(MultibootModule::new(start, end, name)),
            Self::Multiboot2(_) => Module::Multiboot2(todo!()),
        }
    }

     pub fn set_boot_loader_name(&mut self, name: Option<&str>) {
        match self {
            Self::Multiboot(b) => b.with_wrap_mut(|w| w.set_boot_loader_name(name)),
            Self::Multiboot2(b) => todo!(),
        }
    }

    pub fn set_command_line(&mut self, cmdline: Option<&str>) {
        match self {
            Self::Multiboot(b) => b.with_wrap_mut(|w| w.set_command_line(cmdline)),
            Self::Multiboot2(b) => todo!(),
        }
    }

    pub fn set_memory_bounds(&mut self, bounds: Option<(u32, u32)>) {
        match self {
            Self::Multiboot(i) => i.with_wrap_mut(
                |w| w.set_memory_bounds(bounds)
            ),
            Self::Multiboot2(_) => todo!(),
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
            Self::Multiboot2(_) => todo!(),
        }
    }

    pub fn set_memory_regions(&mut self, regions: Option<Vec<MemoryEntry>>) {
        match self {
            Self::Multiboot(b) => b.with_wrap_mut(|w| 
                match regions {
                    None => w.set_memory_regions(None),
                    Some(mods) => {
                        let v: Vec<_> = mods.into_iter().map(|mo|match mo {
                            MemoryEntry::Multiboot(m) => m,
                            MemoryEntry::Multiboot2(_) => panic!("wrong Multiboot version"),
                        }).collect();
                        w.set_memory_regions(Some(
                            (v.as_slice().as_ptr() as u64, v.len())
                        ))
                    }
                }
            ),
            Self::Multiboot2(_) => todo!(),
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
            Self::Multiboot2(_) => todo!(),
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
            Self::Multiboot2(_) => todo!(),
        }
    }
}

#[self_referencing]
pub struct MultibootInfoBuilder {
    info: MultibootInfo,
    allocator: MultibootAllocator,
    #[borrows(mut info, mut allocator)]
    #[not_covariant]
    wrap: Multiboot<'this, 'this>,
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
            Self::Multiboot2(a) => match a.typ() {
                MemoryAreaType::Available => MemoryType::Available,
                MemoryAreaType::Reserved => MemoryType::Reserved,
                MemoryAreaType::AcpiAvailable => MemoryType::AcpiAvailable,
                MemoryAreaType::ReservedHibernate => MemoryType::ReservedHibernate,
                MemoryAreaType::Defective => MemoryType::Defective,
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
    Multiboot2(ModuleTag),
}

#[derive(Clone, Copy)]
pub enum Symbols {
    Multiboot(SymbolType),
    Multiboot2(Option<ElfSectionsTag>),
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
            Self::Multiboot2(_) => todo!(),
        }
    }
}

#[derive(Debug)]
pub enum FramebufferInfo {
    Multiboot(FramebufferTable),
    Multiboot2(FramebufferTag<'static>),
}
