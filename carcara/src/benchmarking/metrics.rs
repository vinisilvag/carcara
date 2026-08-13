use std::{
    cmp, fmt,
    iter::Sum,
    ops::{Add, AddAssign, Sub},
    time::Duration,
};

/// A type that can be used as a unit of measurement for benchmark metrics.
pub trait MetricsUnit:
    Copy + Default + PartialOrd + Add<Output = Self> + AddAssign + Sum + Sub<Output = Self>
{
    /// The type used to represent the mean and standard deviation of the samples.
    ///
    /// This is usually `Self`, but it might be a different type if `Self` is an integer type and we
    /// need non-integer means.
    type MeanType: MetricsUnit;

    /// Converts the value to an `f64`.
    fn as_f64(&self) -> f64;

    /// Creates a mean value from an `f64`.
    fn from_f64(x: f64) -> Self::MeanType;

    /// Divides `self` by a count, producing a mean value.
    fn div_u32(self, rhs: u32) -> Self::MeanType;

    /// Computes the difference between a sample and a mean.
    fn mean_diff(self, mean: Self::MeanType) -> Self::MeanType;

    /// Displays the value into the given formatter.
    fn display(&self, f: &mut fmt::Formatter) -> fmt::Result;

    /// Returns the absolute difference between `self` and `other`.
    fn absolute_diff(self, other: Self) -> Self {
        if self > other {
            self - other
        } else {
            other - self
        }
    }
}

impl MetricsUnit for Duration {
    type MeanType = Self;

    fn as_f64(&self) -> f64 {
        self.as_secs_f64()
    }

    fn from_f64(x: f64) -> Self::MeanType {
        Self::from_secs_f64(x)
    }

    fn div_u32(self, rhs: u32) -> Self::MeanType {
        self / rhs
    }

    fn mean_diff(self, mean: Self::MeanType) -> Self::MeanType {
        self.absolute_diff(mean)
    }

    fn display(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl MetricsUnit for f64 {
    type MeanType = Self;

    fn as_f64(&self) -> f64 {
        *self
    }

    fn from_f64(x: f64) -> Self::MeanType {
        x
    }

    fn div_u32(self, rhs: u32) -> Self::MeanType {
        self / (rhs as f64)
    }

    fn mean_diff(self, mean: Self::MeanType) -> Self::MeanType {
        self - mean
    }

    fn display(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:.04}", self)
    }
}

impl MetricsUnit for usize {
    type MeanType = f64;

    fn as_f64(&self) -> f64 {
        *self as f64
    }

    fn from_f64(x: f64) -> Self::MeanType {
        x
    }

    fn div_u32(self, rhs: u32) -> Self::MeanType {
        self as f64 / rhs as f64
    }

    fn mean_diff(self, mean: Self::MeanType) -> Self::MeanType {
        (self as f64) - mean
    }

    fn display(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

struct DisplayUnit<T: MetricsUnit>(T);

impl<T: MetricsUnit> fmt::Display for DisplayUnit<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.display(f)
    }
}

/// A collection of samples with an associated key, from which aggregate statistics can be
/// computed.
pub trait Metrics<K, T: MetricsUnit>: fmt::Display {
    /// Adds a new sample to the collection.
    fn add_sample(&mut self, key: &K, value: T);

    /// Combines two collections of samples into one.
    fn combine(self, other: Self) -> Self;

    /// Returns `true` if the collection contains no samples.
    fn is_empty(&self) -> bool;

    /// Returns the key and value of the largest sample.
    fn max(&self) -> &(K, T);

    /// Returns the key and value of the smallest sample.
    fn min(&self) -> &(K, T);

    /// Returns the sum of all samples.
    fn total(&self) -> T;

    /// Returns the number of samples.
    fn count(&self) -> usize;

    /// Returns the mean of the samples.
    fn mean(&self) -> T::MeanType;

    /// Returns the standard deviation of the samples.
    fn standard_deviation(&self) -> T::MeanType;
}

fn display_metrics<K, T, M>(metrics: &M, f: &mut fmt::Formatter) -> fmt::Result
where
    T: MetricsUnit,
    M: Metrics<K, T>,
{
    if f.alternate() {
        write!(
            f,
            "{} ({} * {})",
            DisplayUnit(metrics.total()),
            DisplayUnit(metrics.mean()),
            DisplayUnit(metrics.count())
        )
    } else {
        write!(
            f,
            "{} ± {}",
            DisplayUnit(metrics.mean()),
            DisplayUnit(metrics.standard_deviation())
        )
    }
}

/// Metrics whose aggregate statistics are updated incrementally as samples are added.
///
/// This avoids actually storing all samples, reducing the memory footprint, but at the cost of some
/// numerical stability.
#[derive(Debug, Clone)]
pub struct OnlineMetrics<K, T: MetricsUnit = Duration> {
    total: T,
    count: usize,
    mean: T::MeanType,
    max_min: Option<((K, T), (K, T))>,

    /// This is equal to the sum of the square distances of every sample to the mean, that is,
    /// `variance * (n - 1)`. This is used to calculate the standard deviation.
    pub(super) sum_of_squared_distances: f64,
}

impl<K, T: MetricsUnit> OnlineMetrics<K, T> {
    /// Creates a new, empty `OnlineMetrics`.
    pub fn new() -> Self {
        Default::default()
    }
}

impl<K, T: MetricsUnit> Default for OnlineMetrics<K, T> {
    // Ideally, I would like to just `#[derive(Default)]`, but because of a quirk in how `derive`
    // works, that would require the type parameter `K` to always be `Default` as well, even though
    // it is not necessary. Therefore, I have to implement `Default` manually. For more info, see:
    // https://github.com/rust-lang/rust/issues/26925

    fn default() -> Self {
        Self {
            total: T::default(),
            count: 0,
            mean: T::MeanType::default(),
            max_min: None,
            sum_of_squared_distances: 0.0,
        }
    }
}

impl<K: Clone, T: MetricsUnit> fmt::Display for OnlineMetrics<K, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        display_metrics(self, f)
    }
}

impl<K: Clone, T: MetricsUnit> Metrics<K, T> for OnlineMetrics<K, T> {
    /// Adds a new sample to the metrics. This updates all the fields of the struct to equal the
    /// new mean, standard deviation, etc. For simplicity, these are calculated every time a new
    /// sample is added, which means you can stop adding samples at any time and the metrics will
    /// always be valid.
    fn add_sample(&mut self, key: &K, value: T) {
        let old_mean = self.mean;

        self.total += value;
        self.count += 1;
        self.mean = self.total.div_u32(self.count as u32);

        // We calculate the new variance using Welford's algorithm. See:
        // https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Welford's_online_algorithm
        let variance_delta =
            value.mean_diff(self.mean).as_f64() * value.mean_diff(old_mean).as_f64();
        self.sum_of_squared_distances += variance_delta;

        match &mut self.max_min {
            Some((max, min)) => {
                // If there are ties for `min` or `max`, we take the first value.
                if value > max.1 {
                    *max = (key.clone(), value);
                }
                if value < min.1 {
                    *min = (key.clone(), value);
                }
            }
            None => self.max_min = Some(((key.clone(), value), (key.clone(), value))),
        }
    }

    /// Combines two metrics into one. If one the metrics has only one data point, this is
    /// equivalent to `Metrics::add_sample`. This is generally numerically stable if the metrics
    /// have many data points, or exactly one. If one of the metrics is small, the error in the
    /// variance introduced by using this method (as opposed to using `Metrics::add_sample` on each
    /// data point) can be as high as 30%.
    fn combine(self, other: Self) -> Self {
        match (self.count, other.count) {
            (0, _) => return other,
            (_, 0) => return self,
            (1, _) => {
                let mut result = other;
                let only_entry = self.min();
                result.add_sample(&only_entry.0, only_entry.1);
                return result;
            }
            (_, 1) => return other.combine(self),
            _ => (),
        }
        let total = self.total + other.total;
        let count = self.count + other.count;
        let mean = total.div_u32(count as u32);

        // To combine the two variances, we use a generalization of Welford's algorithm. See:
        // https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Parallel_algorithm
        let delta = other.mean.absolute_diff(self.mean).as_f64();
        let sum_of_squared_distances = self.sum_of_squared_distances
            + other.sum_of_squared_distances
            + delta * delta * (self.count * other.count / count) as f64;

        let max_min = match (self.max_min, other.max_min) {
            (a, None) => a,
            (None, b) => b,
            (Some((a_max, a_min)), Some((b_max, b_min))) => {
                let max = if a_max.1 > b_max.1 { a_max } else { b_max };
                let min = if a_min.1 < b_min.1 { a_min } else { b_min };
                Some((max, min))
            }
        };

        Self {
            total,
            count,
            mean,
            max_min,
            sum_of_squared_distances,
        }
    }

    fn is_empty(&self) -> bool {
        self.count == 0
    }

    fn max(&self) -> &(K, T) {
        &self.max_min.as_ref().unwrap().0
    }

    fn min(&self) -> &(K, T) {
        &self.max_min.as_ref().unwrap().1
    }

    fn total(&self) -> T {
        self.total
    }

    fn count(&self) -> usize {
        self.count
    }

    fn mean(&self) -> T::MeanType {
        self.mean
    }

    fn standard_deviation(&self) -> T::MeanType {
        let count = cmp::max(2, self.count) - 1;
        T::from_f64((self.sum_of_squared_distances / count as f64).sqrt())
    }
}

/// Metrics that store every sample and compute aggregate statistics on demand.
///
/// This is more numerically stable than [`OnlineMetrics`], but can use a lot more memory.
pub struct OfflineMetrics<K, T = Duration> {
    data: Vec<(K, T)>,
}

impl<K, T: MetricsUnit> OfflineMetrics<K, T> {
    /// Creates a new, empty `OfflineMetrics`.
    pub fn new() -> Self {
        Default::default()
    }

    /// Sorts the samples and returns the values at the 5%, 25%, 50%, 75%, and 95% percentiles.
    pub fn quartiles(&mut self) -> [&(K, T); 5] {
        assert!(!self.data.is_empty());
        self.data
            .sort_unstable_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
        let n = self.data.len();
        [n / 20, n / 4, n / 2, (n * 3) / 4, (n * 19) / 20].map(|i| &self.data[i])
    }
}

impl<K, T: MetricsUnit> Default for OfflineMetrics<K, T> {
    fn default() -> Self {
        Self { data: Vec::new() }
    }
}

impl<K: Clone, T: MetricsUnit> fmt::Display for OfflineMetrics<K, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        display_metrics(self, f)
    }
}

impl<K: Clone, T: MetricsUnit> Metrics<K, T> for OfflineMetrics<K, T> {
    fn add_sample(&mut self, key: &K, value: T) {
        self.data.push((key.clone(), value));
    }

    fn combine(mut self, mut other: Self) -> Self {
        self.data.append(&mut other.data);
        self
    }

    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    fn max(&self) -> &(K, T) {
        self.data
            .iter()
            .max_by(|a, b| PartialOrd::partial_cmp(&a.1, &b.1).unwrap_or(cmp::Ordering::Equal))
            .unwrap()
    }

    fn min(&self) -> &(K, T) {
        self.data
            .iter()
            .min_by(|a, b| PartialOrd::partial_cmp(&a.1, &b.1).unwrap_or(cmp::Ordering::Equal))
            .unwrap()
    }

    fn total(&self) -> T {
        self.data.iter().map(|(_, v)| *v).sum()
    }

    fn count(&self) -> usize {
        self.data.len()
    }

    fn mean(&self) -> T::MeanType {
        self.total().div_u32(self.count() as u32)
    }

    fn standard_deviation(&self) -> T::MeanType {
        let mean = self.mean();
        let sum_of_squared_distances: f64 = self
            .data
            .iter()
            .map(|&(_, v)| {
                let delta = v.mean_diff(mean).as_f64();
                delta * delta
            })
            .sum();
        let variance = sum_of_squared_distances / (cmp::max(2, self.count()) - 1) as f64;
        T::from_f64(variance.sqrt())
    }
}
