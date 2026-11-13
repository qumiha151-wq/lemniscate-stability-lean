module
public import ClosureFixture.A

@[expose] public section
namespace ClosureFixture
def b : Nat := a + 1
theorem b_eq : b = 8 := rfl
end ClosureFixture
