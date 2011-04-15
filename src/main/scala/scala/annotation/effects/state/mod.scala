package scala.annotation.effects
package state

class fresh extends Effect
class mod(locations: Any*) extends Effect
class modAll extends Effect

class local extends scala.annotation.StaticAnnotation // this is not an effect
