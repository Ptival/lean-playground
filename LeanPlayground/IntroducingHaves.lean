def f (x : Int) : Int :=
  have a := 2
  a + a + x + a

theorem test : f 2 = 2 := by
  unfold f
  conv =>
    left
    intro a
