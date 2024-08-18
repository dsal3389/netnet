use std::error::Error;
use std::fmt::Display;
use std::net::Ipv4Addr;
use std::ops::Deref;

type Result<T> = std::result::Result<T, NetnetError>;

#[derive(Debug, PartialEq)]
pub enum NetnetError {
    InvalidSubnet(String),
}

impl std::fmt::Display for NetnetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSubnet(reason) => write!(f, "invalid mask: {}", reason),
        }
    }
}

impl Error for NetnetError {}

/// the AddressV4 type used to represent single ipv4 address
/// the uses `std::net::Ipv4Addr` under the hood, and implement &Deref
/// that returns the underlying address, so anywhere you use `Ipv4Addr` you will be able
/// to also use `AddressV4`
#[derive(Clone, PartialEq, Debug)]
pub struct AddressV4 {
    address: Ipv4Addr,
}

/// uses to distinguish between regular addresses and subnets, this type
/// also have constraints when created to make sure the given subnet
/// is a valid subnet mask
#[derive(Clone, PartialEq, Debug)]
pub struct SubnetV4 {
    subnet: AddressV4,
}

/// a pair of `AddressV4` and `SubnetV4` to represent a network address,
/// based on the pair it is possible to create supernets and subnets
#[derive(Clone, PartialEq, Debug)]
pub struct NetworkV4 {
    address: AddressV4,
    subnet: SubnetV4,
}

impl AddressV4 {
    pub fn new(a: u8, b: u8, c: u8, d: u8) -> Self {
        Self {
            address: Ipv4Addr::new(a, b, c, d),
        }
    }
}

impl NetworkV4 {
    pub fn new(address: AddressV4, subnet: SubnetV4) -> Self {
        // TODO normilize address to network address
        Self { address, subnet }
    }

    /// returns the network address
    pub fn address(&self) -> &Ipv4Addr {
        &self.address
    }

    /// returns the network subnet
    pub fn subnet(&self) -> &SubnetV4 {
        &self.subnet
    }

    /// returns the network broadcast address, if the
    /// network subnet mask is /32, then the return value
    /// will be equal to the return value of the `address` function
    pub fn broadcast(&self) -> AddressV4 {
        if self.subnet.host_bits() == 0 {
            self.address.clone()
        } else {
            let jumps = u32::pow(2, self.subnet.host_bits());
            (self.address.to_bits() + jumps - 1).into()
        }
    }

    /// returns the number of hosts
    /// available in the network
    pub fn available_hosts(&self) -> u32 {
        u32::pow(2, self.subnet.host_bits()).saturating_sub(2)
    }
}

impl SubnetV4 {
    pub fn new(a: u8, b: u8, c: u8, d: u8) -> Result<Self> {
        Ok(Self {
            subnet: AddressV4::new(a, b, c, d),
        })
    }

    /// returns the subnet mask as cidr number
    #[inline]
    pub fn cidr(&self) -> u32 {
        self.subnet.to_bits().leading_ones()
    }

    /// returns how many host bits
    /// in the subnet are going for the network
    #[inline]
    pub fn networ_bits(&self) -> u32 {
        self.cidr()
    }

    /// returns how many host bits
    /// in the subnet are going for the hosts
    #[inline]
    pub fn host_bits(&self) -> u32 {
        self.subnet.to_bits().trailing_zeros()
    }
}

impl Display for AddressV4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.address)
    }
}

impl Display for NetworkV4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.address, self.subnet)
    }
}

impl Display for SubnetV4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.subnet)
    }
}

impl From<[u8; 4]> for AddressV4 {
    fn from(value: [u8; 4]) -> Self {
        Self::new(value[0], value[1], value[2], value[3])
    }
}

impl From<u32> for AddressV4 {
    fn from(value: u32) -> Self {
        let octets = value.to_be_bytes();
        Self::from(octets)
    }
}

impl From<(AddressV4, SubnetV4)> for NetworkV4 {
    fn from(value: (AddressV4, SubnetV4)) -> Self {
        Self::new(value.0, value.1)
    }
}

impl TryFrom<([u8; 4], [u8; 4])> for NetworkV4 {
    type Error = NetnetError;
    fn try_from(value: ([u8; 4], [u8; 4])) -> std::prelude::v1::Result<Self, Self::Error> {
        let subnet = SubnetV4::try_from(value.1)?;
        Ok(Self::new(value.0.into(), subnet))
    }
}

impl TryFrom<u32> for SubnetV4 {
    type Error = NetnetError;
    fn try_from(value: u32) -> std::prelude::v1::Result<Self, Self::Error> {
        Self::try_from(Ipv4Addr::from(value))
    }
}

impl TryFrom<[u8; 4]> for SubnetV4 {
    type Error = NetnetError;
    fn try_from(value: [u8; 4]) -> std::prelude::v1::Result<Self, Self::Error> {
        Self::try_from(Ipv4Addr::from(value))
    }
}

impl TryFrom<Ipv4Addr> for SubnetV4 {
    type Error = NetnetError;
    fn try_from(value: Ipv4Addr) -> std::prelude::v1::Result<Self, Self::Error> {
        let octets = value.octets();
        Self::new(octets[0], octets[1], octets[2], octets[3])
    }
}

impl Deref for AddressV4 {
    type Target = Ipv4Addr;
    fn deref(&self) -> &Self::Target {
        &self.address
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_network_broadcast() {
        let network = NetworkV4::new(
            AddressV4::new(10, 0, 0, 0),
            SubnetV4::new(255, 255, 255, 255).unwrap(),
        );
        assert_eq!(network.broadcast(), AddressV4::new(10, 0, 0, 0));

        let network = NetworkV4::new(
            AddressV4::new(192, 168, 32, 16),
            SubnetV4::new(255, 255, 255, 240).unwrap(),
        );
        assert_eq!(network.broadcast(), AddressV4::new(192, 168, 32, 31));
    }

    #[test]
    fn test_available_hosts() {
        let network: NetworkV4 = ([10, 0, 0, 0], [255, 255, 255, 0]).try_into().unwrap();
        assert_eq!(network.available_hosts(), 254);

        let network: NetworkV4 = ([192, 168, 1, 0], [255, 224, 0, 0]).try_into().unwrap();
        assert_eq!(network.available_hosts(), 2_097_150)
    }

    #[test]
    fn test_subnet_cidr() {
        let subnet = SubnetV4::new(255, 255, 255, 248).unwrap();
        assert_eq!(subnet.cidr(), 29);

        let subnet = SubnetV4::new(255, 255, 255, 255).unwrap();
        assert_eq!(subnet.cidr(), 32);

        let subnet = SubnetV4::new(255, 224, 0, 0).unwrap();
        assert_eq!(subnet.cidr(), 11);
    }

    #[test]
    fn test_network_to_string() {
        let network = NetworkV4::new(
            AddressV4::new(10, 0, 0, 0),
            SubnetV4::new(255, 255, 255, 0).unwrap(),
        );
        assert_eq!(network.to_string(), "10.0.0.0/255.255.255.0");
    }

    #[test]
    fn test_subnet_to_string() {
        let subnet = SubnetV4::new(255, 255, 0, 0).unwrap();
        assert_eq!(subnet.to_string(), "255.255.0.0");

        let subnet = SubnetV4::new(255, 32, 0, 0).unwrap();
        assert_eq!(subnet.to_string(), "255.32.0.0");
    }
}
