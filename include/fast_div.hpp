///
/// @file  fast_div.hpp
/// @brief Integer division of small types is much faster than integer
///        division of large types on most CPUs. The fast_div(x, y)
///        function tries to take advantage of this by casting x and y
///        to smaller types (if possible) before doing the division.
///
///        If ENABLE_DIV32 is defined we check at runtime if the
///        dividend and divisor are < 2^32 and if so we use 32-bit
///        integer division instead of 64-bit integer division. On
///        most CPUs before 2020 this significantly improves
///        performance.
///
///        On some new CPUs (such as Intel Cannonlake) 64-bit integer
///        division has been improved significantly and runs as fast
///        as 32-bit integer division. For such CPUs it is best to
///        disable ENABLE_DIV32 (using cmake -DWITH_DIV32=OFF) as this
///        avoids runtime checks for (64-bit / 32-bit) divisions.
///
/// Copyright (C) 2020 Kim Walisch, <kim.walisch@gmail.com>
///
/// This file is distributed under the BSD License. See the COPYING
/// file in the top level directory.
///

#ifndef FAST_DIV_HPP
#define FAST_DIV_HPP

#include <cassert>
#include <limits>
#include <stdint.h>
#include <type_traits>

namespace {

/// If ENABLE_DIV32 is defined:
///
/// 1) We use 32-bit integer division for (64-bit / 32-bit)
///    if the dividend is < 2^32.
/// 2) We use 64-bit integer division for (64-bit / 64-bit).
/// 3) We use 64-bit integer division for (128-bit / 64-bit)
///    if the dividend is < 2^64.
///
#if defined(ENABLE_DIV32)

/// Get the next smaller integer type
/// and convert it to unsigned.
/// make_smaller< uint64_t>::type -> uint32_t.
/// make_smaller<uint128_t>::type -> uint64_t.
///
template <typename T>
struct make_smaller
{
  using type = typename std::conditional<sizeof(T) / 2 <= sizeof(uint32_t), uint32_t,
               typename std::conditional<sizeof(T) / 2 <= sizeof(uint64_t), uint64_t,
               T>::type>::type;
};

/// Used for (64-bit / 64-bit) = 64-bit.
template <typename X, typename Y>
typename std::enable_if<(sizeof(X) == sizeof(Y)), X>::type
fast_div(X x, Y y)
{
  // Unsigned integer division is usually
  // faster than signed integer division.
  using UX = typename std::make_unsigned<X>::type;
  return (UX) x / (UX) y;
}

/// Used for  (64-bit / 32-bit) =  64-bit.
/// Used for (128-bit / 64-bit) = 128-bit.
template <typename X, typename Y>
typename std::enable_if<(sizeof(X) > sizeof(Y)), X>::type
fast_div(X x, Y y)
{
  using smaller_t = typename make_smaller<X>::type;

  if (x <= std::numeric_limits<smaller_t>::max())
    return (smaller_t) x / (smaller_t) y;
  else
  {
    // Unsigned integer division is usually
    // faster than signed integer division.
    using UX = typename std::make_unsigned<X>::type;
    using UY = typename std::make_unsigned<Y>::type;
    return (UX) x / (UY) y;
  }
}

#else

/// If ENABLE_DIV32 is not defined:
///
/// 1) We use 64-bit integer division for (64-bit / 32-bit).
/// 2) We use 64-bit integer division for (64-bit / 64-bit).
/// 3) We use 64-bit integer division for (128-bit / 64-bit)
///    if the dividend is < 2^64.
///

/// Get the next smaller integer type
/// and convert it to unsigned.
/// make_smaller<uint128_t>::type -> uint64_t.
///
template <typename T>
struct make_smaller
{
  using type = typename std::make_unsigned<
                 typename std::conditional<
                   sizeof(T) == sizeof(uint64_t) * 2,
                     uint64_t, T>::type>::type;
};

/// Used for (64-bit / 32-bit) = 64-bit.
/// Used for (64-bit / 64-bit) = 64-bit.
template <typename X, typename Y>
typename std::enable_if<(sizeof(X) >= sizeof(Y) &&
                         sizeof(X) <= sizeof(uint64_t)), X>::type
fast_div(X x, Y y)
{
  // Unsigned integer division is usually
  // faster than signed integer division.
  using UX = typename std::make_unsigned<X>::type;
  return (UX) x / (UX) y;
}

/// Used for (128-bit / 64-bit) = 128-bit.
template <typename X, typename Y>
typename std::enable_if<(sizeof(X) > sizeof(Y) &&
                         sizeof(X) > sizeof(uint64_t)), X>::type
fast_div(X x, Y y)
{
  using smaller_t = typename make_smaller<X>::type;

  if (x <= std::numeric_limits<smaller_t>::max())
    return (smaller_t) x / (smaller_t) y;
  else
  {
    // Unsigned integer division is usually
    // faster than signed integer division.
    using UX = typename std::make_unsigned<X>::type;
    using UY = typename std::make_unsigned<Y>::type;
    return (UX) x / (UY) y;
  }
}

#endif

/// Used for (128-bit / 64-bit) = 64-bit.
/// Use this function only when you know for sure
/// that the result is < 2^64.
///
template <typename X, typename Y>
typename std::enable_if<(sizeof(X) == sizeof(uint64_t) * 2 &&
                         sizeof(Y) <= sizeof(uint64_t)), uint64_t>::type
fast_div64(X x, Y y)
{
#if defined(__x86_64__) && \
   (defined(__GNUC__) || defined(__clang__))

  // primecount does not need signed division so 
  // we use the unsigned division instruction further
  // down as DIV is usually faster than IDIV.
  assert(x >= 0 && y > 0);

  uint64_t x0 = (uint64_t) x;
  uint64_t x1 = ((uint64_t*) &x)[1];
  uint64_t d = y;

  // (128-bit / 64-bit) = 64-bit.
  // When we know the result fits into 64-bit (even
  // though the numerator is 128-bit) we can use the divq
  // instruction instead of doing a full 128-bit division.
  __asm__("divq %[divider]"
          : "+a"(x0), "+d"(x1) : [divider] "r"(d));

  return x0;
#else
  return (uint64_t) fast_div(x, y);
#endif
}

/// Used for (64-bit / 32-bit) = 64-bit.
/// Used for (64-bit / 64-bit) = 64-bit.
template <typename X, typename Y>
typename std::enable_if<!(sizeof(X) == sizeof(uint64_t) * 2 &&
                          sizeof(Y) <= sizeof(uint64_t)), uint64_t>::type
fast_div64(X x, Y y)
{
  return (uint64_t) fast_div(x, y);
}

// Faster (?) division for the case where a single dividend (m) is
// divided by a (decreasing) sequence of divisors (t). We compute the
// division result by using a linear approximation, and then check the
// result by multiplying it back by the divisor. If the check fails,
// we recompute the approximation parameters.
template <typename T>
class SequenceDivider {
public:
  explicit SequenceDivider(T m) :
    m(m), t_base(0), result_base(0), slope_shifted(0) {}

  inline uint64_t DivideBy(uint64_t t) {
    if (t < min_t) return fast_div64(m, t);

    uint64_t result = result_base + (((t_base - t) * slope_shifted) >> shift);

    uint64_t error = m - result * t;
    if (__builtin_expect(error < 3*t, true)) {
      result_base += (error >= 2*t);
      return result + (error >= t) + (error >= 2*t);
    }

    // The error is too big, recompute the approximation.
    result_base = fast_div64(m, t);
    slope_shifted = fast_div64(T(result_base) << shift, t);
    t_base = t;
    return result_base;
  }

private:
  static constexpr int shift = 16;
  static constexpr uint64_t min_t = 1 << 17;
  const T m;
  uint64_t t_base, result_base, slope_shifted;

  // Implementation notes:
  //
  // 1. This optmization probably makes sense only for processors with
  // a slow divider, for example, Skylake and earlier.
  //
  // 2. The values of shift and min_t could use some tuning.
  //
  // 3. It would be more accurate to compute result_base shifted, in a
  // similar way as we compute slope_shifted, but that could overflow T.
  //
  // 4. Initializing non-const member fields is not needed, but the
  // compiler complains otherwise.
};

} // namespace

#endif
