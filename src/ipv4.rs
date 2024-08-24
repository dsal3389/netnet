use std::fmt::Display;
use std::net::Ipv4Addr;
use std::ops::Deref;

use crate::{NetnetError, Result};

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
pub struct NetmaskV4 {
    netmask: AddressV4,
}

/// a pair of `AddressV4` and `NetmaskV4` to represent a network address,
/// based on the pair it is possible to create supernets and subnets
#[derive(Clone, PartialEq, Debug)]
pub struct NetworkV4 {
    address: AddressV4,
    netmask: NetmaskV4,
}

/// the network dealer class is more like a network provider, you need a
/// network that can contain 45 hosts, you as the dealer to give you a new network that
/// can contain 45 hosts.
///
/// the dealer doesn't generates random networks for you to use, the dealer starts from
/// the network 1.0.0.0/0 and every time you ask for a new network, the dealer will given you
/// the new network with respect to what he previously gave you.
///
/// ```
/// use netnet::{NetworkV4Dealer, NetworkV4};
///
/// let mut dealer = NetworkV4Dealer::new();
///
/// let network_a = dealer.for_hostn(45).unwrap();
/// assert_eq!(network_a, NetworkV4::try_from((
///     [1, 0, 0, 0],
///     [255, 255, 255, 192]
/// )).unwrap());
///
/// let network_b = dealer.for_hostn(5).unwrap();
/// assert_eq!(network_b, NetworkV4::try_from((
///     [1, 0, 0, 64],
///     [255, 255, 255, 248]
/// )).unwrap());
/// ```
///
/// `network_b` is starting from the end of `network_a`, so the returned network does not conflict
/// with different networks.
#[derive(Clone, PartialEq, Debug)]
pub struct NetworkV4Dealer {
    network: NetworkV4,
}

impl AddressV4 {
    pub fn new(a: u8, b: u8, c: u8, d: u8) -> Self {
        Self {
            address: Ipv4Addr::new(a, b, c, d),
        }
    }
}

impl NetworkV4 {
    pub fn new(address: AddressV4, netmask: NetmaskV4) -> Self {
        // TODO normilize address to network address
        Self { address, netmask }
    }

    /// returns the network address
    #[inline]
    pub fn address(&self) -> AddressV4 {
        self.address.clone()
    }

    /// returns the network netmask
    #[inline]
    pub fn netmask(&self) -> NetmaskV4 {
        self.netmask.clone()
    }

    /// returns the network broadcast address, if the
    /// network subnet mask is /32, then the return value
    /// will be equal to the return value of the `address` function
    pub fn broadcast(&self) -> AddressV4 {
        if self.netmask.host_bits() == 0 {
            return self.address.clone();
        }
        let jumps = u32::pow(2, self.netmask.host_bits());
        return (self.address.to_bits() + jumps - 1).into();
    }
    /// returns the number of addresses that can be used for host in the network
    #[inline]
    pub fn available_hosts(&self) -> u32 {
        // -2 because the network and broadcast addresses
        u32::pow(2, self.netmask.host_bits()).saturating_sub(2)
    }

    /// gets a smaller network prefix from the current network `cidr`, and
    /// sub-nets the current network to smaller network chunks based on the given prefix
    /// note that the prefix must be a valid prefix from 1-32
    ///
    /// ```
    /// use netnet::NetworkV4;
    ///
    /// let network = NetworkV4::try_from((
    ///     [10, 0, 0, 0],
    ///     [255, 0, 0, 0]
    /// )).unwrap();
    ///
    /// assert_eq!(network.netmask().cidr(), 8);
    ///
    /// let subnets = network.subnets(24).unwrap();
    /// let first = subnets.first().unwrap();
    /// assert_eq!(first.netmask().cidr(), 24);
    /// ```
    pub fn subnets(&self, prefix: u32) -> Result<Vec<NetworkV4>> {
        if prefix < self.netmask.cidr() {
            return Err(NetnetError::InvalidPrefix(prefix));
        }

        let mut subnets = Vec::<NetworkV4>::new();
        let prefix_delta = prefix - self.netmask.cidr();

        if prefix_delta == 0 {
            subnets.push(self.clone());
            return Ok(subnets);
        }

        let start = u32::from(self.address.clone());
        let end = u32::from(self.broadcast());
        let step: u32 = (0xffffffff >> prefix) + 1;

        for address in (start..end).step_by(step as usize) {
            let netmask = NetmaskV4::from_prefix(prefix)?;
            let address = AddressV4::from(address);
            subnets.push(NetworkV4::from((address, netmask)));
        }
        Ok(subnets)
    }
}

impl NetmaskV4 {
    pub const MIN_CIDR: u32 = 0;
    pub const MAX_CIDR: u32 = 32;

    pub fn new(a: u8, b: u8, c: u8, d: u8) -> Result<Self> {
        Ok(Self {
            netmask: AddressV4::new(a, b, c, d),
        })
    }

    /// creates netmask from prefix number
    /// ```
    /// use netnet::NetmaskV4;
    ///
    /// let netmask = NetmaskV4::from_prefix(24);
    /// assert_eq!(netmask, NetmaskV4::new(255, 255, 255, 0));
    /// ```
    #[inline]
    pub fn from_prefix(prefix: u32) -> Result<NetmaskV4> {
        let delta = Self::MAX_CIDR - prefix;
        Self::try_from(0xffffffff << delta)
    }

    /// returns the subnet mask as cidr number
    /// alias to `network_bits`
    #[inline]
    pub fn cidr(&self) -> u32 {
        self.network_bits()
    }

    /// returns how many bits
    /// in the subnet are going for the network
    #[inline]
    pub fn network_bits(&self) -> u32 {
        self.netmask.to_bits().leading_ones()
    }

    /// returns how many bits
    /// in the subnet are going for the hosts
    #[inline]
    pub fn host_bits(&self) -> u32 {
        self.netmask.to_bits().trailing_zeros()
    }
}

impl NetworkV4Dealer {
    pub fn new() -> Self {
        Self {
            network: NetworkV4::new(0x01000000.into(), 0.try_into().unwrap()),
        }
    }

    pub fn for_hostn(&mut self, hostn: u32) -> Option<NetworkV4> {
        let new_netmask = NetmaskV4::from_prefix(Self::cidr_for_hostn(hostn)).unwrap();
        let new_netmask_jumps = u32::pow(2, new_netmask.cidr());
        let jumps = u32::pow(2, self.network.netmask.cidr());

        // if case `jumps` eq to 1, it is likely that this is
        // the first call to `for_hostn` and the initilized
        // netmask was `0`
        let network_address = if jumps == 1 {
            self.network.address()
        } else {
            let mut network = u32::from(*self.network.address) + jumps;
            while network % new_netmask_jumps != 0 {
                network += jumps;
            }
            AddressV4::from(network)
        };

        self.network = NetworkV4::from((network_address, new_netmask));
        Some(self.network.clone())
    }

    /// returns the smallest cidr number for a network
    /// that can contain the given required hosts number
    #[inline]
    pub fn cidr_for_hostn(hostn: u32) -> u32 {
        hostn.leading_zeros()
    }
}

impl Display for AddressV4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.address)
    }
}

impl Display for NetmaskV4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.netmask)
    }
}

impl Display for NetworkV4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.address, self.netmask)
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

impl From<(AddressV4, NetmaskV4)> for NetworkV4 {
    fn from(value: (AddressV4, NetmaskV4)) -> Self {
        Self::new(value.0, value.1)
    }
}

impl TryFrom<(u32, u32)> for NetworkV4 {
    type Error = NetnetError;
    fn try_from(value: (u32, u32)) -> std::prelude::v1::Result<Self, Self::Error> {
        let netmask = NetmaskV4::try_from(value.1)?;
        Ok(Self::new(value.0.into(), netmask))
    }
}

impl From<AddressV4> for u32 {
    fn from(value: AddressV4) -> Self {
        u32::from(value.address)
    }
}

impl From<NetmaskV4> for u32 {
    fn from(value: NetmaskV4) -> Self {
        u32::from(value.netmask)
    }
}

impl From<AddressV4> for Ipv4Addr {
    fn from(value: AddressV4) -> Self {
        value.address
    }
}

impl From<NetmaskV4> for Ipv4Addr {
    fn from(value: NetmaskV4) -> Self {
        value.netmask.into()
    }
}

impl TryFrom<([u8; 4], [u8; 4])> for NetworkV4 {
    type Error = NetnetError;
    fn try_from(value: ([u8; 4], [u8; 4])) -> std::prelude::v1::Result<Self, Self::Error> {
        let subnet = NetmaskV4::try_from(value.1)?;
        Ok(Self::new(value.0.into(), subnet))
    }
}

impl TryFrom<u32> for NetmaskV4 {
    type Error = NetnetError;
    fn try_from(value: u32) -> std::prelude::v1::Result<Self, Self::Error> {
        Self::try_from(Ipv4Addr::from(value))
    }
}

impl TryFrom<[u8; 4]> for NetmaskV4 {
    type Error = NetnetError;
    fn try_from(value: [u8; 4]) -> std::prelude::v1::Result<Self, Self::Error> {
        Self::try_from(Ipv4Addr::from(value))
    }
}

impl TryFrom<Ipv4Addr> for NetmaskV4 {
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
    fn test_network_for_hostn() {
        let mut network_dealer = NetworkV4Dealer::new();
        let network = network_dealer.for_hostn(5).unwrap();

        assert_eq!(
            network,
            NetworkV4::try_from((0x01000000, 0xfffffff8)).unwrap()
        );
    }

    #[test]
    fn test_network_dealer_cidr_calc() {
        assert_eq!(NetworkV4Dealer::cidr_for_hostn(5), 29);
        assert_eq!(NetworkV4Dealer::cidr_for_hostn(44), 26)
    }

    #[test]
    fn test_network_subnets() {
        let network: NetworkV4 = ([10, 0, 0, 0], [255, 255, 255, 0]).try_into().unwrap();
        let subnets = network.subnets(25).unwrap();

        assert_eq!(
            subnets,
            vec![
                NetworkV4::try_from(([10, 0, 0, 0], [255, 255, 255, 128])).unwrap(),
                NetworkV4::try_from(([10, 0, 0, 128], [255, 255, 255, 128])).unwrap()
            ]
        );

        let network: NetworkV4 = ([192, 168, 0, 0], [255, 255, 224, 0]).try_into().unwrap();
        assert_eq!(
            *network.subnets(24).unwrap().first().unwrap(),
            NetworkV4::try_from(([192, 168, 0, 0], [255, 255, 255, 0])).unwrap(),
        )
    }

    #[test]
    fn test_network_broadcast() {
        let network = NetworkV4::new(
            AddressV4::new(10, 0, 0, 0),
            NetmaskV4::new(255, 255, 255, 255).unwrap(),
        );
        assert_eq!(network.broadcast(), AddressV4::new(10, 0, 0, 0));

        let network = NetworkV4::new(
            AddressV4::new(192, 168, 32, 16),
            NetmaskV4::new(255, 255, 255, 240).unwrap(),
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
    fn test_prefix_cidr() {
        let netmask = NetmaskV4::new(255, 255, 255, 248).unwrap();
        assert_eq!(netmask.cidr(), 29);

        let netmask = NetmaskV4::new(255, 255, 255, 255).unwrap();
        assert_eq!(netmask.cidr(), 32);

        let netmask = NetmaskV4::new(255, 224, 0, 0).unwrap();
        assert_eq!(netmask.cidr(), 11);
    }

    #[test]
    fn test_netmask_from_prefix() {
        let netmask = NetmaskV4::from_prefix(25).unwrap();
        assert_eq!(netmask, NetmaskV4::new(255, 255, 255, 128).unwrap());
    }

    #[test]
    fn test_network_to_string() {
        let network = NetworkV4::new(
            AddressV4::new(10, 0, 0, 0),
            NetmaskV4::new(255, 255, 255, 0).unwrap(),
        );
        assert_eq!(network.to_string(), "10.0.0.0/255.255.255.0");
    }

    #[test]
    fn test_netmask_to_string() {
        let netmask = NetmaskV4::new(255, 255, 0, 0).unwrap();
        assert_eq!(netmask.to_string(), "255.255.0.0");

        let netmask = NetmaskV4::new(255, 32, 0, 0).unwrap();
        assert_eq!(netmask.to_string(), "255.32.0.0");
    }
}
