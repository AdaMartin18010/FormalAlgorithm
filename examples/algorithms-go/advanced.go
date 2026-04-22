// Package algorithms provides advanced algorithm implementations in Go.
package algorithms

import (
	"math"
	"math/rand"
)

// SimulatedAnnealing finds an approximate minimum of an energy function.
func SimulatedAnnealing(initial float64, neighbor func(float64) float64, energy func(float64) float64) float64 {
	current := initial
	currentEnergy := energy(current)
	best := current
	bestEnergy := currentEnergy
	temp := 1.0
	coolingRate := 0.9999
	for i := 0; i < 100000; i++ {
		next := neighbor(current)
		nextEnergy := energy(next)
		delta := nextEnergy - currentEnergy
		if delta < 0 || rand.Float64() < math.Exp(-delta/temp) {
			current = next
			currentEnergy = nextEnergy
			if currentEnergy < bestEnergy {
				best = current
				bestEnergy = currentEnergy
			}
		}
		temp *= coolingRate
	}
	return best
}
