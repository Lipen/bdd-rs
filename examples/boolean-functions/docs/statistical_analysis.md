# Statistical Analysis Methods

This document covers the statistical methods used for analyzing BDD size distributions via Monte Carlo sampling.

## The Sampling Problem

For $n$ variables, there are $2^{2^n}$ Boolean functions. Beyond $n = 4$, exhaustive enumeration is infeasible:

| n | Functions | Enumeration Time |
|---|-----------|------------------|
| 4 | 65,536 | < 1 second |
| 5 | 4.3 billion | Hours |
| 6 | $1.8 \times 10^{19}$ | Impossible |

We must use **statistical sampling** and make inferences about the population from samples.

## Basic Statistics

### Sample Mean

The sample mean estimates the population mean:

$$\bar{X} = \frac{1}{n} \sum_{i=1}^n X_i$$

By the **Law of Large Numbers**, $\bar{X} \to \mu$ as $n \to \infty$.

### Sample Variance

The unbiased sample variance:

$$s^2 = \frac{1}{n-1} \sum_{i=1}^n (X_i - \bar{X})^2$$

### Standard Error

The standard error of the mean:

$$SE = \frac{s}{\sqrt{n}}$$

This measures the precision of our estimate of $\mu$.

## Confidence Intervals

A **confidence interval** is a range that contains the true parameter with specified probability.

### Central Limit Theorem (CLT)

For large $n$, the sample mean is approximately normal:

$$\bar{X} \sim N\left(\mu, \frac{\sigma^2}{n}\right)$$

The $(1-\alpha)$ confidence interval:

$$\bar{X} \pm z_{\alpha/2} \cdot \frac{s}{\sqrt{n}}$$

where $z_{\alpha/2}$ is the $(1-\alpha/2)$ quantile of the standard normal.

Common values:

- 90% CI: $z = 1.645$
- 95% CI: $z = 1.96$
- 99% CI: $z = 2.576$

### Student's t-Distribution

For smaller samples, use the t-distribution:

$$\bar{X} \pm t_{\alpha/2, n-1} \cdot \frac{s}{\sqrt{n}}$$

The t-distribution has heavier tails and accounts for uncertainty in estimating $\sigma$.

### Interpretation

A 95% confidence interval does NOT mean "95% probability the true mean is in this range."

Rather: if we repeated the sampling many times, 95% of the constructed intervals would contain the true mean.

## Bootstrap Methods

**Bootstrap resampling** is a nonparametric method that:

1. Resamples with replacement from the data
2. Computes the statistic for each resample
3. Uses the empirical distribution of the statistic

### Percentile Bootstrap

1. Draw $B$ bootstrap samples (typically $B = 1000$ to $10000$)
2. Compute $\bar{X}^*_1, \ldots, \bar{X}^*_B$
3. The $(1-\alpha)$ CI is $[\hat{Q}_{\alpha/2}, \hat{Q}_{1-\alpha/2}]$

where $\hat{Q}_p$ is the $p$-th quantile of the bootstrap distribution.

### What is the Bootstrap Distribution?

The **bootstrap distribution** is *not* a known theoretical distribution (like Normal or t).  It is the empirical distribution of your statistic, constructed from resamples of your data.

**How to obtain it**:

1. Take your original sample of size $n$
2. Draw $B$ bootstrap samples by sampling $n$ observations *with replacement*
3. Compute the statistic of interest (mean, median, etc.) for each bootstrap sample
4. The resulting $B$ values $\{\theta^*_1, \ldots, \theta^*_B\}$ form the bootstrap distribution

This empirical distribution approximates the true (unknown) sampling distribution of your statistic.

### Advantages

- Works for **any statistic** (mean, median, variance, correlation, quantiles, ratios)
- Makes **no distributional assumptions** about the population
- Provides accurate intervals even for **skewed distributions**
- Automatically captures the correct shape of the sampling distribution

### Limitations

- Requires the sample to be representative of the population
- Can be slow for very large datasets or complex statistics
- May perform poorly for very small samples ($n < 15$)
- Doesn't work well for statistics at the boundary (e.g., sample maximum)

### Bootstrap Standard Error

$$SE_{boot} = \sqrt{\frac{1}{B-1} \sum_{b=1}^B (\theta^*_b - \bar{\theta}^*)^2}$$

where $\bar{\theta}^* = \frac{1}{B}\sum_{b=1}^B \theta^*_b$ is the mean of bootstrap estimates.

For the sample mean, this should be close to the analytical SE $s/\sqrt{n}$.

## Tail Bounds and Concentration Inequalities

### Chebyshev's Inequality

For any distribution with mean $\mu$ and variance $\sigma^2$:

$$P(|X - \mu| \geq k\sigma) \leq \frac{1}{k^2}$$

This is **distribution-free** but often loose.

For the sample mean:

$$P(|\bar{X} - \mu| \geq k \cdot SE) \leq \frac{1}{k^2}$$

### Hoeffding's Inequality

For bounded random variables $X_i \in [a, b]$:

$$P(\bar{X} - \mu \geq \epsilon) \leq \exp\left(-\frac{2n\epsilon^2}{(b-a)^2}\right)$$

**Sample size requirement**: To achieve $P(|\bar{X} - \mu| \geq \epsilon) \leq \delta$:

$$n \geq \frac{(b-a)^2 \ln(2/\delta)}{2\epsilon^2}$$

### Chernoff Bounds

For sums of independent Bernoulli random variables:

$$P\left(\sum_{i=1}^n X_i \geq (1+\delta)\mu\right) \leq \exp\left(-\frac{\delta^2 \mu}{2+\delta}\right)$$

These give exponentially decreasing tail probabilities.

## Comparing Methods

The choice of method depends on your goal, sample size, and what you know about the distribution.

### Summary Table

| Method | Assumptions | Best For | Tightness |
|--------|-------------|----------|-----------|
| CLT CI | $n \gtrsim 30$, finite variance | Mean estimation | Tight |
| t-dist CI | Normality or $n \gtrsim 15$ | Small-sample means | Tight |
| Bootstrap | i.i.d. samples | Medians, quantiles, ratios | Tight |
| Chebyshev | Finite variance only | Guaranteed probability bounds | Very loose |
| Hoeffding | Bounded support $[a,b]$ | Tail probabilities, sample size | Moderate |
| Chernoff | Sum of independent $[0,1]$ RVs | Multiplicative deviations | Tight for Bernoulli sums |

### Confidence Intervals vs. Tail Bounds

**Confidence intervals** (CLT, t-distribution, Bootstrap) answer: *"Where does the true parameter likely lie?"*

- They give an interval $[L, U]$ such that $P(\mu \in [L, U]) \geq 1 - \alpha$
- The interval is random (depends on sample); the parameter is fixed

**Tail bounds** (Chebyshev, Hoeffding, Chernoff) answer: *"What's the probability of a large deviation?"*

- They bound $P(|\bar{X} - \mu| \geq \epsilon)$ from above
- Useful for worst-case analysis and determining required sample sizes

### Tightness vs. Generality Trade-off

- **Chebyshev**: Works for *any* distribution with finite variance, but the bound $1/k^2$ is often 10-100× larger than the true probability
- **Hoeffding**: Requires bounded support, but gives exponentially decreasing bounds — much tighter than Chebyshev
- **Chernoff**: Most specific (requires Bernoulli sums), but tightest bounds for that setting
- **CLT/Bootstrap**: Make distributional assumptions but give the most accurate intervals

### When to Use What

1. **CLT/t-distribution**:
   - Default for estimating means with $n > 30$
   - Use t-distribution for $n < 30$ or when you want slightly wider (more conservative) intervals
   - Fast, simple, well-understood

2. **Bootstrap**:
   - Estimating non-mean statistics: medians, quantiles, variance, correlation, ratios
   - When the underlying distribution is skewed or unknown
   - When you want to avoid parametric assumptions
   - Computational cost: requires $B = 1000$–$10000$ resamples

3. **Chebyshev**:
   - When you need a *guaranteed* bound with *no* distributional assumptions
   - For quick back-of-envelope calculations
   - Accept that it will be very conservative (often 10× looser than reality)

4. **Hoeffding**:
   - Theoretical analysis when support $[a, b]$ is known
   - Determining sample size requirements for given precision
   - Gives exponential decay: $\exp(-2n\epsilon^2/(b-a)^2)$

5. **Chernoff**:
   - Sums of Bernoulli/indicator random variables
   - Analyzing *multiplicative* deviations: $P(X \geq (1+\delta)\mu)$
   - Common in randomized algorithms and probabilistic analysis

## Sample Size Determination

### For Confidence Intervals

To achieve margin of error $\epsilon$ with confidence $(1-\alpha)$:

$$n \geq \left(\frac{z_{\alpha/2} \cdot \sigma}{\epsilon}\right)^2$$

If $\sigma$ is unknown, use a pilot study or conservative estimate.

### For Relative Precision

To estimate the mean within $p$% of its value:

$$n \geq \left(\frac{z_{\alpha/2} \cdot CV}{p}\right)^2$$

where $CV = \sigma/\mu$ is the coefficient of variation.

## Variance Reduction Techniques

### Stratified Sampling

Divide the population into strata and sample from each:

$$\bar{X}_{str} = \sum_h W_h \bar{X}_h$$

where $W_h$ is the stratum weight.

This reduces variance if strata are more homogeneous than the population.

### Antithetic Variates

For each random sample, also use its "opposite":

If $U$ is uniform, also use $1-U$.

This induces negative correlation and reduces variance.

## Practical Considerations

### Convergence Checking

Monitor the running estimate and its standard error. Stop when:

- SE is small enough (relative to mean)
- Estimates have stabilized

### Reporting Results

Always report:

1. Sample size
2. Point estimate
3. Standard error or confidence interval
4. Method used

Example: "Mean BDD size = 7.52 ± 0.15 (95% CI: [7.23, 7.81], n = 10000, CLT)"

### Computational Cost

Balance between:

- More samples → better precision
- Each sample → BDD construction cost

For our BDD application: construction is fast for small $n$, dominates for large $n$.

## References

1. B. Efron & R. Tibshirani, "An Introduction to the Bootstrap"
2. W. Hoeffding, "Probability Inequalities for Sums of Bounded Random Variables"
3. L. Wasserman, "All of Statistics"
4. J. Shao & D. Tu, "The Jackknife and Bootstrap"
