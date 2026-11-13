module
public import ClosureFixture.B

@[expose] public section
namespace ClosureFixture
def c : Nat := b + 1
theorem c_eq : c = 9 := rfl
end ClosureFixture
