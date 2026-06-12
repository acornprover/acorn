use std::fmt;
use std::str::FromStr;

use sha2::{Digest, Sha256};

pub const GOAL_BUCKET_COUNT: u8 = 100;

/// Stable partition bucket for a goal identity.
///
/// The bucket is the first eight bytes, big-endian, of SHA-256 over
/// `"{module}\t{goal}"`, modulo 100. Do not replace this with Rust's default
/// hasher; eval and training partitions need to stay reproducible across
/// processes, toolchains, and languages.
pub fn goal_bucket(module: &str, goal: &str) -> u8 {
    let mut hasher = Sha256::new();
    hasher.update(module.as_bytes());
    hasher.update(b"\t");
    hasher.update(goal.as_bytes());
    let digest = hasher.finalize();
    let first_eight: [u8; 8] = digest[..8]
        .try_into()
        .expect("sha256 digest is long enough");
    (u64::from_be_bytes(first_eight) % u64::from(GOAL_BUCKET_COUNT)) as u8
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct GoalBucketRange {
    start: u8,
    end: u8,
}

impl GoalBucketRange {
    fn contains(&self, bucket: u8) -> bool {
        self.start <= bucket && bucket <= self.end
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoalBucketFilter {
    ranges: Vec<GoalBucketRange>,
}

impl GoalBucketFilter {
    pub fn contains(&self, bucket: u8) -> bool {
        self.ranges.iter().any(|range| range.contains(bucket))
    }

    pub fn single(bucket: u8) -> Self {
        assert!(bucket < GOAL_BUCKET_COUNT);
        Self {
            ranges: vec![GoalBucketRange {
                start: bucket,
                end: bucket,
            }],
        }
    }
}

impl fmt::Display for GoalBucketFilter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, range) in self.ranges.iter().enumerate() {
            if index > 0 {
                write!(f, ",")?;
            }
            if range.start == range.end {
                write!(f, "{}", range.start)?;
            } else {
                write!(f, "{}-{}", range.start, range.end)?;
            }
        }
        Ok(())
    }
}

impl FromStr for GoalBucketFilter {
    type Err = String;

    fn from_str(raw: &str) -> Result<Self, Self::Err> {
        let raw = raw.trim();
        if raw.is_empty() {
            return Err("bucket range must not be empty".to_string());
        }

        let mut ranges = Vec::new();
        for part in raw.split(',') {
            let part = part.trim();
            if part.is_empty() {
                return Err("bucket range contains an empty entry".to_string());
            }

            let (start, end) = match part.split_once('-') {
                Some((start, end)) => (parse_bucket(start)?, parse_bucket(end)?),
                None => {
                    let bucket = parse_bucket(part)?;
                    (bucket, bucket)
                }
            };
            if start > end {
                return Err(format!(
                    "bucket range start {} is greater than end {}",
                    start, end
                ));
            }
            ranges.push(GoalBucketRange { start, end });
        }

        Ok(Self { ranges })
    }
}

fn parse_bucket(raw: &str) -> Result<u8, String> {
    let bucket = raw
        .trim()
        .parse::<u8>()
        .map_err(|_| format!("invalid bucket '{}'", raw))?;
    if bucket >= GOAL_BUCKET_COUNT {
        return Err(format!(
            "bucket {} is out of range; expected 0-{}",
            bucket,
            GOAL_BUCKET_COUNT - 1
        ));
    }
    Ok(bucket)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn goal_bucket_uses_stable_test_vectors() {
        assert_eq!(goal_bucket("foo", "first"), 54);
        assert_eq!(goal_bucket("real.cbrt", "some_goal"), 29);
        assert_eq!(
            goal_bucket("number_theory.arithmetic_functions", "multiplicative_one"),
            60
        );
    }

    #[test]
    fn bucket_filter_parses_ranges() {
        let filter: GoalBucketFilter = "0-4, 17, 90-94".parse().unwrap();
        assert!(filter.contains(0));
        assert!(filter.contains(4));
        assert!(filter.contains(17));
        assert!(filter.contains(90));
        assert!(filter.contains(94));
        assert!(!filter.contains(5));
        assert!(!filter.contains(89));
        assert_eq!(filter.to_string(), "0-4,17,90-94");
    }

    #[test]
    fn bucket_filter_rejects_bad_ranges() {
        assert!("".parse::<GoalBucketFilter>().is_err());
        assert!("100".parse::<GoalBucketFilter>().is_err());
        assert!("9-3".parse::<GoalBucketFilter>().is_err());
        assert!("1,,2".parse::<GoalBucketFilter>().is_err());
    }
}
