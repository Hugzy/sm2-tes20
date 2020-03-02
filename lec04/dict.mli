type dictionary
type key = string
type value = int
val empty : dictionary
val add : dictionary -> key -> value -> dictionary
val find : dictionary -> key -> value