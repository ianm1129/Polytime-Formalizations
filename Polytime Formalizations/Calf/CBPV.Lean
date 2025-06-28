
namespace CBPV


axiom tp_pos : Type
axiom tp_neg : Type
axiom val : tp_pos → Type


axiom F : tp_pos → tp_neg
axiom U : tp_neg → tp_pos

def cmp (X : tp_neg) : Type := val (U X)


variable {A B C : tp_pos}
variable {X Y Z : tp_neg}


--value types

axiom meta_pos : Type → tp_pos
axiom meta_pos_decode : {S : Type} → val (meta_pos S) = S

noncomputable
def Sigma_pos (A : tp_pos) (B : val A → tp_pos) : tp_pos :=
      meta_pos (Σ x : (val A), val (B x))



--computation types

axiom ret : val A → cmp (F A)
axiom bind : (X : tp_neg) → cmp (F A) → (val A → cmp X) → cmp X
axiom bind_β {a : val A} {f : val A → cmp X} : bind X (ret a) f = f a
axiom bind_η {e : cmp (F A)} : bind (F A) e ret = e
axiom bind_assoc {e : cmp (F A)} {f : val A → cmp (F B)} {g : val B → cmp X} :
      bind X (bind (F B) e f) g = bind X e (fun a => bind X (f a) g)

axiom Pi (A : tp_pos) (X : val A → tp_neg) : tp_neg
axiom Pi_decode {X : val A → tp_neg} :
                val (U (Pi A X)) = ((a : val A) → cmp (X a))

axiom prod_neg : tp_neg → tp_neg → tp_neg
axiom prod_neg_decode : val (U (prod_neg X Y)) = (cmp X × cmp Y)

axiom unit_neg : tp_neg
axiom unit_neg_decode : val (U unit_neg) = Unit

axiom Sigma_neg (A : tp_pos) (X : val A → tp_neg) : tp_neg
axiom Sigma_neg_decode {X : val A → tp_neg} :
                      val (U (Sigma_neg A X)) = Σ a : (val A), (cmp (X a))

noncomputable
def ltimes (A : tp_pos) (X : tp_neg) : tp_neg := Sigma_neg A (fun _ => X)

--Todo : make this infix using ⋉ if possible
