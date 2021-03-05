{
  type bool = unit + unit

  signature EQ = {
    type t
    val eq : t & t -> bool
  }

  signature ORD = {
    include EQ
    val less : t & t -> bool
  }

  signature SET = {
    type set
    type elem
    val empty : set
    val add : elem & set -> set
    val mem : elem & set -> bool
  }
}
