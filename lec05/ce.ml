module H1 =
  struct
    type cmd =
      | Add of string * int
      | Remove of string
      | Find of string
      | Mem of string [@@deriving show]
  end

module H2 =
  struct
    type cmd =
      | Add of string * int
      | Remove of string
      | Find of string
      | Mem of string [@@deriving show { with_path = false }]
  end