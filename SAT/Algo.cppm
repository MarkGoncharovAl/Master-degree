module;

#include <bitset>

export module Algo;

export import <optional>;
export import Sat;

namespace detail {

template <size_t N>
std::optional<std::bitset<N>>
simplestFind(const Sat::Sat_t &Sat, size_t VarCount = N,
             std::bitset<N> VarSets = std::bitset<N>{});

} // namespace detail

export namespace Algo {

bool simplestCheck(const Sat::Sat_t &Sat, size_t VarCount = 0);

template <size_t N>
std::optional<std::string> simplestFind(const Sat::Sat_t &Sat);

} // namespace Algo

// -------------- Implementations ------------------------------------

bool Algo::simplestCheck(const Sat::Sat_t &Sat, size_t VarCount) {
  if (VarCount == 0)
    return Sat;
  return simplestCheck(Sat.setVar(VarCount), VarCount - 1) ||
         simplestCheck(Sat.setVar(-VarCount), VarCount - 1);
}

template <size_t N>
std::optional<std::string> Algo::simplestFind(const Sat::Sat_t &Sat) {
  auto VarSet = detail::simplestFind<N>(Sat);
  if (!VarSet)
    return std::nullopt;
  std::string result = "";
  for (size_t i = 0; i < N; ++i) {
    result += VarSet->test(i) ? "x" : "~x";
    result += std::to_string(i + 1) + " ";
  }
  return result;
}

template <size_t N>
std::optional<std::bitset<N>> detail::simplestFind(const Sat::Sat_t &Sat,
                                                   size_t VarCount,
                                                   std::bitset<N> VarSets) {
  if (VarCount == 0)
    return Sat ? std::make_optional(VarSets) : std::nullopt;

  if (auto Set = simplestFind(Sat.setVar(-VarCount), VarCount - 1, VarSets))
    return Set;

  std::bitset<N> NextVarSets = VarSets;
  NextVarSets.set(VarCount - 1);

  if (auto Set = simplestFind(Sat.setVar(VarCount), VarCount - 1, NextVarSets))
    return Set;
  return std::nullopt;
}