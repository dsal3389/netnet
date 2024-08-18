use std::error::Error;
use std::net::Ipv4Addr;

type Result<T> = std::result::Result<T, RanddressError>;

#[derive(Debug, PartialEq)]
pub enum RanddressError {
    InvalidMask(String),
}

impl std::fmt::Display for RanddressError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidMask(reason) => write!(f, "invalid mask: {}", reason),
        }
    }
}

impl Error for RanddressError {}

// returns `Ipv4Addr` representing subnet mask, the
// given argument `bit_index` shifts the `u32::MAX` to the left
// representing a valid netmask
//
// 0xffffffff << 4 = 0xfffffff0 = 255.255.255.251
// this cidr can contain 4 addresses
#[inline]
fn mask_by_bit(bit_index: u32) -> Ipv4Addr {
    Ipv4Addr::from(u32::MAX << bit_index)
}

// returns the last bit index that was `1` in the given number
// counting starts from one
#[inline]
fn first_bit_on(n: u32) -> u32 {
    u32::BITS - n.leading_zeros()
}

/// structure representing pair of network address
/// and its subnet mask, the address should NOT point to a host
/// address (unless its a 32 bit mask), it points to the network address
pub struct NetworkV4 {
    address: Ipv4Addr,
    mask: Ipv4Addr,
}

/// structure that generates networks with respect
/// to the network subnet masks
pub struct NetworkV4Generator {
    state: [Option<NetworkV4>; u32::BITS as usize],
    last_address: Option<NetworkV4>,
}

impl NetworkV4Generator {
    pub fn new() -> Self {
        Self {
            state: [const { None }; u32::BITS as usize],
            last_address: None,
        }
    }

    pub fn start_from(network: NetworkV4) -> Self {
        Self {
            state: [const { None }; u32::BITS as usize],
            last_address: Some(network),
        }
    }

    /// returns how may addresses available, calculated based on
    /// the last generated address
    pub fn available(&self) -> u32 {
        if let Some(network) = &self.last_address {
            return u32::MAX - network.broadcast().to_bits();
        }
        return u32::MAX;
    }

    pub fn take(&mut self, n: u32) -> Vec<Ipv4Addr> {
        todo!()
    }
}

impl Default for NetworkV4Generator {
    fn default() -> Self {
        Self::new()
    }
}

impl NetworkV4 {
    pub fn new(address: Ipv4Addr, mask: Ipv4Addr) -> Result<Self> {
        // if mask.to_bits() > u32::BITS {
        //     return Err(RanddressError::InvalidMask(
        //         format!("impossible mask")
        //     );
        // }
        Ok(Self { address, mask })
    }

    /// returns the network address
    pub fn address(&self) -> &Ipv4Addr {
        &self.address
    }

    /// returns the network mask
    pub fn mask(&self) -> &Ipv4Addr {
        &self.mask
    }

    /// returns the network broadcast address, if network
    /// is 32 bit mask, then there is only 1 address and thats
    /// equal to `address`
    pub fn broadcast(&self) -> Ipv4Addr {
        let subnet_bit = self.mask.to_bits().trailing_zeros();
        let last_address = self
            .address
            .to_bits()
            .saturating_sub(1)
            .saturating_add(u32::pow(2, subnet_bit));
        return Ipv4Addr::from(last_address);
    }
}

impl From<(Ipv4Addr, Ipv4Addr)> for NetworkV4 {
    fn from(value: (Ipv4Addr, Ipv4Addr)) -> Self {
        Self {
            address: value.0,
            mask: value.1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_availability() {
        let start_address = NetworkV4::new(
            Ipv4Addr::new(255, 255, 255, 0),
            Ipv4Addr::new(255, 255, 255, 0),
        )
        .unwrap();
        let network_generator = NetworkV4Generator::start_from(start_address);

        assert_eq!(network_generator.available(), 0);

        let network_generator = NetworkV4Generator::start_from(
            NetworkV4::new(
                Ipv4Addr::new(255, 255, 254, 0),
                Ipv4Addr::new(255, 255, 255, 0),
            )
            .unwrap(),
        );
        assert_eq!(network_generator.available(), 255)
    }

    #[test]
    fn test_network_broadcast() {
        let network = NetworkV4::new(
            Ipv4Addr::new(10, 0, 0, 0),
            Ipv4Addr::new(255, 255, 255, 248),
        )
        .unwrap();
        assert_eq!(network.broadcast(), Ipv4Addr::new(10, 0, 0, 7));

        let network = NetworkV4::new(
            Ipv4Addr::new(192, 168, 1, 1),
            Ipv4Addr::new(255, 255, 255, 255),
        )
        .unwrap();
        assert_eq!(network.broadcast(), Ipv4Addr::new(192, 168, 1, 1));

        let network = NetworkV4::new(
            Ipv4Addr::new(192, 168, 1, 0),
            Ipv4Addr::new(255, 255, 255, 0),
        )
        .unwrap();
        assert_eq!(network.broadcast(), Ipv4Addr::new(192, 168, 1, 255));

        let network = NetworkV4::new(
            Ipv4Addr::new(255, 255, 255, 0),
            Ipv4Addr::new(255, 255, 255, 0),
        )
        .unwrap();
        assert_eq!(network.broadcast(), Ipv4Addr::new(255, 255, 255, 255));
    }

    #[test]
    fn test_turned_on_bit() {
        assert_eq!(first_bit_on(4), 3);
        assert_eq!(first_bit_on(8), 4);
        assert_eq!(first_bit_on(14), 4);
        assert_eq!(first_bit_on(78), 7);
    }

    #[test]
    fn test_mask_for_bit_index() {
        assert_eq!(mask_by_bit(7), Ipv4Addr::new(255, 255, 255, 128));
        assert_eq!(mask_by_bit(9), Ipv4Addr::new(255, 255, 254, 0));
    }
}
