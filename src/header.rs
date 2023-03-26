use core::pin::Pin;
use alloc::boxed::Box;
use ouroboros::self_referencing;

use multiboot::header::{
    Header as MultibootHeader,
    MultibootAddresses,
    MultibootVideoMode,
    VideoModeType,
};
use multiboot2_header::{
    AddressHeaderTag,
    ConsoleHeaderTag,
    FramebufferHeaderTag,
    Multiboot2Header,
};

use super::information::{InfoBuilder, Symbols};

#[derive(Debug)]
pub enum Header {
    Multiboot(MultibootHeader),
    Multiboot2(Multiboot2HeaderWrap),
}

impl Header {
    pub fn from_slice(buffer: &[u8]) -> Option<Self> {
        match Multiboot2HeaderWrap::from_slice(buffer) {
            Some(w) => Some(Header::Multiboot2(w)),
            None => MultibootHeader::from_slice(buffer).map(
                |h| Header::Multiboot(h)
            ),
        }
    }

    pub fn header_start(&self) -> u32 {
        match self {
            Self::Multiboot(h) => h.header_start,
            Self::Multiboot2(h) => *h.borrow_header_start(),
        }
    }

    pub fn get_preferred_video_mode(&self) -> Option<VideoMode> {
        match self {
            Self::Multiboot(h) => h.get_preferred_video_mode().map(|vm| VideoMode::Multiboot(vm)),
            Self::Multiboot2(h) => {
                if let Some(fb) = h.borrow_header().framebuffer_tag() {
                    Some(VideoMode::Multiboot2(Multiboot2VideoMode::LinearGraphics(fb)))
                } else {
                    if let Some(ct) = h.borrow_header().console_flags_tag() {
                        Some(VideoMode::Multiboot2(Multiboot2VideoMode::TextMode(ct)))
                    } else {
                        None
                    }
                }
            }
        }
    }

    pub fn get_load_addresses(&self) -> Option<Addresses> {
        match self {
            Self::Multiboot(h) => h.get_addresses().map(
                |a| Addresses::Multiboot(a)
            ),
            Self::Multiboot2(h) => {
                h.borrow_header()
                    .address_tag()
                    .map(|a| Addresses::Multiboot2(*a))
            }
        }
    }

    pub fn get_entry_address(&self) -> Option<u32> {
        match self {
            Self::Multiboot(h) => h.get_addresses().map(
                |a| a.entry_address
            ),
            Self::Multiboot2(h) => {
                h.borrow_header().entry_address_tag().map(
                    |t| t.entry_addr()
                )
            }
        }
    }

    pub fn info_builder(&self) -> InfoBuilder {
        match self {
            Self::Multiboot(_) => InfoBuilder::new_multiboot(),
            Self::Multiboot2(_) => InfoBuilder::new_multiboot2(),
        }
    }

    pub fn new_elf_symbols(
        &self, num: u32, size: u32, addr: usize, shndx: u32
    ) -> Symbols {
        match self {
            Self::Multiboot(_) => Symbols::new_multiboot(
                num, size, addr, shndx
            ),
            Self::Multiboot2(_) => Symbols::new_multiboot2(
                num, size, addr, shndx
            ),
        }
    }
}

#[self_referencing]
#[derive(Debug)]
pub struct Multiboot2HeaderWrap {
    header_pin: Pin<Box<[u8]>>,
    header_start: u32,
    #[borrows(header_pin)]
    #[covariant]
    header: Multiboot2Header<'this>,
}

impl Multiboot2HeaderWrap {
    fn from_slice(buffer: &[u8]) -> Option<Self> {
        // first, find the header
        let (header_buf, header_start) = Multiboot2Header::find_header(buffer)?;
        // then, copy it
        let header_pin = Box::into_pin(header_buf.to_vec().into_boxed_slice());
        Some(Multiboot2HeaderWrapBuilder {
            header_pin,
            header_start,
            header_builder: |header_pin: &Pin<Box<[u8]>>| unsafe {
                // yes, that's bad, but making it better would mean modifying
                // the multiboot2 crate
                Multiboot2Header::from_addr(
                    header_pin.as_ref().as_ptr() as usize
                )
            }
        }.build())
    }
}


pub enum Addresses {
    Multiboot(MultibootAddresses),
    Multiboot2(AddressHeaderTag),
}

impl Addresses {
    pub fn compute_load_offset(&self, header_start: u32) -> u32 {
        match self {
            Self::Multiboot(a) => a.compute_load_offset(header_start),
            Self::Multiboot2(a) => header_start - (
                a.header_addr() - a.load_addr()
            ),
        }
    }

    pub fn compute_kernel_length(&self, whole_length: u32) -> u32 {
        if self.bss_end_addr() == 0 {
            if self.load_end_addr() == 0 {
                self.header_addr() + whole_length - self.load_addr()
            } else {
                self.load_end_addr() - self.load_addr()
            }
        } else {
            self.bss_end_addr() - self.load_addr()
        }
    }

    fn header_addr(&self) -> u32 {
        match self {
            Self::Multiboot(a) => a.header_address,
            Self::Multiboot2(a) => a.header_addr(),
        }
    }

    fn bss_end_addr(&self) -> u32 {
        match self {
            Self::Multiboot(a) => a.bss_end_address,
            Self::Multiboot2(a) => a.bss_end_addr(),
        }
    }

    pub fn load_addr(&self) -> u32 {
        match self {
            Self::Multiboot(a) => a.load_address,
            Self::Multiboot2(a) => a.load_addr(),
        }
    }

    pub fn load_end_addr(&self) -> u32 {
        match self {
            Self::Multiboot(a) => a.load_end_address,
            Self::Multiboot2(a) => a.load_end_addr(),
        }
    }
}

pub enum VideoMode<'a> {
    Multiboot(MultibootVideoMode),
    Multiboot2(Multiboot2VideoMode<'a>),
}

impl VideoMode<'_> {
    pub fn is_graphics(&self) -> bool {
        match self {
            Self::Multiboot(vm) => match vm.mode_type() {
                Some(VideoModeType::LinearGraphics) => true,
                _ => false,
            },
            Self::Multiboot2(Multiboot2VideoMode::LinearGraphics(_)) => true,
            _ => false,
        }
    }

    pub fn depth(&self) -> Option<u32> {
        match self {
            Self::Multiboot(vm) => vm.depth(),
            Self::Multiboot2(Multiboot2VideoMode::LinearGraphics(&ft)) => {
                Some(ft.depth())
            },
            _ => None,
        }
    }

    /// Return the width of the framebuffer.
    /// Text consoles in multiboot2 have no size.
    pub fn width(&self) -> Option<u32> {
        match self {
            Self::Multiboot(vm) => Some(vm.width),
            Self::Multiboot2(Multiboot2VideoMode::LinearGraphics(&ft)) => {
                Some(ft.width())
            },
            Self::Multiboot2(Multiboot2VideoMode::TextMode(_)) => None,
        }
    }

    /// Return the height of the framebuffer.
    /// Text consoles in multiboot2 have no size.
    pub fn height(&self) -> Option<u32> {
        match self {
            Self::Multiboot(vm) => Some(vm.height),
            Self::Multiboot2(Multiboot2VideoMode::LinearGraphics(&ft)) => {
                Some(ft.height())
            },
            Self::Multiboot2(Multiboot2VideoMode::TextMode(_)) => None,
        }
    }
}


pub enum Multiboot2VideoMode<'a> {
    LinearGraphics(&'a FramebufferHeaderTag),
    TextMode(&'a ConsoleHeaderTag),
}
