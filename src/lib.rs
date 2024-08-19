use std::error::Error;

mod ipv4;
mod ipv6;

pub use ipv4::{AddressV4, NetmaskV4, NetworkV4};
pub use ipv6::AddressV6;

pub enum Address {
    V4(AddressV4),
    V6(AddressV6),
}

pub type Result<T> = std::result::Result<T, NetnetError>;

#[derive(Debug, PartialEq)]
pub enum NetnetError {
    InvalidSubnet(String),
    InvalidPrefix(u32),
}

impl std::fmt::Display for NetnetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSubnet(reason) => write!(f, "invalid mask: {}", reason),
            Self::InvalidPrefix(prefix) => write!(f, "invalid netmask provided `{}`", prefix),
        }
    }
}

impl Error for NetnetError {}
