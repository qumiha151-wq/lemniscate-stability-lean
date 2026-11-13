module

@[expose] public section
namespace ClosureFixture
def a : Nat := 7
private theorem hidden : a = 7 := rfl
theorem a_eq : a = 7 := hidden
end ClosureFixture
