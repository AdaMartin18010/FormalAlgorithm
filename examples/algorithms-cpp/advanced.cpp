/**
 * advanced.cpp - C++高级算法实现
 * 包含: 模拟退火
 */

#include <vector>
#include <cmath>
#include <random>
#include <functional>

namespace advanced {

/**
 * 模拟退火（离散版本）
 */
double simulatedAnnealing(const std::vector<double>& arr,
                           std::function<double(double)> neighborFn,
                           std::function<double(double)> energyFn) {
    double current = arr.empty() ? 0.0 : arr[0];
    double currentEnergy = energyFn(current);
    double best = current;
    double bestEnergy = currentEnergy;
    double temp = 1.0;
    double coolingRate = 0.9999;
    std::mt19937 rng(42);
    std::uniform_real_distribution<double> dist(0.0, 1.0);
    for (int i = 0; i < 100000; i++) {
        double next = neighborFn(current);
        double nextEnergy = energyFn(next);
        double delta = nextEnergy - currentEnergy;
        if (delta < 0 || dist(rng) < std::exp(-delta / temp)) {
            current = next;
            currentEnergy = nextEnergy;
            if (currentEnergy < bestEnergy) {
                best = current;
                bestEnergy = currentEnergy;
            }
        }
        temp *= coolingRate;
    }
    return best;
}

} // namespace advanced
