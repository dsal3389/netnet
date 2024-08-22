use std::{net::Ipv6Addr, ops::Deref};

#[derive(Clone, PartialEq, Debug)]
pub struct AddressV6 {
    address: Ipv6Addr,
}

#[derive(Clone, PartialEq, Debug)]
pub struct NetmaskV6 {
    netmask: AddressV6,
}

#[derive(Clone, PartialEq, Debug)]
pub struct NetworkV6 {
    address: AddressV6,
    netmask: NetmaskV6,
}

impl NetworkV6 {
    pub fn new(address: AddressV6, netmask: NetmaskV6) -> Self {
        Self { address, netmask }
    }

    pub fn network(&self) -> AddressV6 {
        self.address.clone()
    }
}

impl Deref for AddressV6 {
    type Target = Ipv6Addr;
    fn deref(&self) -> &Self::Target {
        &self.address
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
