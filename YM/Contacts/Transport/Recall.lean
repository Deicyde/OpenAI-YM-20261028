import YM.Contacts.Transport.Geometry
import YM.Contacts.Score.Wings
/-! # Naturality of the Jacobi evolution

A congruence between scores that can be queried when restricting the test to a fiber of a bigger
ambient. Covers also transforming the real basis and a permutation/padded embedding of the cluster
points. Orthogonal dichotomy on normalization of the measure addressed separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Transport
open Function Set Normal Submodule Ordered MultipleContact Panel
open scoped Topology Classical BigOperators ContDiff TensorProduct InnerProductSpace
variable {E F : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
  [NormedAddCommGroup F][InnerProductSpace ℝ F][FiniteDimensional ℝ F]
variable {k n : ℕ}{U:E→ₗᵢ[ℝ] F}{P : E→ₗᵢ[ℝ] Points k}{T : F→ₗᵢ[ℝ] Points n}
 {f g : Normal.Group k}{t:Fin k↪ Fin n}{o:Points k}{o' : Points n}{c:F}{s : Ortho}{w : E4}
variable {b : Bool}

/-- whether or not to conjugate while transporting. -/
def realChange (b : Bool) : ℂ →L[ℝ] ℂ:= if b then Complex.conjCLE.toContinuousLinearMap else ContinuousLinearMap.id _ _
lemma apply_change (b : Bool)(x : ℂ) : realChange b x=if b then star x else x:= by cases b <;> rfl
lemma change_one (b:Bool) : realChange b 1=1:=by rw [apply_change]; simp
lemma change_mul (b:Bool) (x y : ℂ) : realChange b (x*y)= realChange b x*realChange b y:= by simp_rw [apply_change]; cases b; rfl; simp [star_mul,mul_comm]
lemma again (b:Bool)(x:ℂ) : realChange b (realChange b x)=x:= by simp_rw [apply_change]; cases b; rfl; simp
lemma reChange (b:Bool)(x:ℝ) : realChange b x=x:= by
   rw [apply_change]; split; · simp
   rfl

def follows (b : Bool) (L : E→ F)(p : SmoothTests E)(q : SmoothTests F) := ∀ i, q.val (L i)= realChange b (p.val i)
-- pullback the parameter to display such f too
def sampling (U : E→ₗᵢ[ℝ] F)(c:F)(b:Bool)(q:SmoothTests F): SmoothTests E:= ⟨fun x=> realChange b (q.val (U x+c)),(realChange b).contDiff.comp ((infSmooth q).comp (U.toContinuousLinearMap.contDiff.add contDiff_const))⟩
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma siblings (q:SmoothTests F) : follows b (fun x=> U x+c) (sampling U c b q) q:= fun _=> (again ..).symm

variable {A B I I' : Type} [CommRing A] [Algebra ℂ A][CommRing B][Algebra ℂ B]{σ : A →+* B}
def Alike (b : Bool)(L:E→F)(p : Optical E)(q : Optical F) := ∀ x y,follows b L x y → follows b L (p x) (q y)
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma Alike.times {L:E→F}{p p':Optical E}{q q':Optical F}(h : Alike b L p q)(hp:Alike b L p' q') : Alike b L (p*p') (q*q'):= fun x y e=> h _ _ (hp x y e)
variable (R : Ribbon t P T U c o o' s w g)
include R
local notation "L" => fun (x:E)=> U x+c
local notation "V" => normalOn T (current t g)
local notation "K!" => normalOn P g
lemma alike_piece (n : ℕ)(hg : g.Nonempty)(b : Bool) : Alike b L (piece K! n) (piece V n) := by
   intro x y h i; let p:= scaledField K! x; let q:= scaledField V y; let f(t:ℝ):=p (i,t); let X:= (L) i; let g(t:ℝ):=q (X,t);
   have hi (a:ℝ) : g a=realChange b (f a):= by unfold g f p q scaledField; rw [← R.retreat i a hg]; exact h _
   have ht: ContDiff ℝ ∞ f:= (onScale ..).comp (contDiff_const.prodMk contDiff_id)
   have hu:=(atoms_equal K! x n 1 i).symm; have hm:=(atoms_equal V y n 1 X).symm; rw [slide_one, Normal.vat] at hu hm; -- fill contdiff
   · rw [hu, hm]; change coeff n g 1= realChange b (coeff n f 1); unfold coeff; rw [show g=(realChange b) ∘ f from funext hi,map_smul,(realChange b).iteratedFDeriv_comp_left ht.contDiffAt (le_inf_order n)]; rfl
   exacts [onScale ..,onScale ..]
lemma taylor_both (u : ℝ)(n : ℕ) (hg:g.Nonempty)(b:Bool) : Alike b L (taylor K! u n) (taylor V u n):= by
   intro p q hp i; change (taylor V u n q).val ((L) i)=_; rw [taylor_formula,taylor_formula,map_smul]; have hx: cutoff u ((look K!).read i)=cutoff u ((look V).read ((L) i)):= by
       unfold cutoff; have he:‖(look V).read ((L) i)‖=‖(look K!).read i‖:= by change ‖(V).starProjection (U i+c)‖=‖(K!).starProjection i‖; rw [R.shaded i hg,U.norm_map]; -- end hep
       rw [he]
   unfold Lens.atoms; rw [hx,map_sum]; exact congrArg ((cutoff u ((look V).read ((L) i))) • ·) (Finset.sum_congr rfl fun j _=> alike_piece R j hg b p q hp i) -- fill
omit R

-- equivalently relative `Mark` on both bits. Supports turn operations before forming integrals. Not weakening relation to equality of tests.
inductive Recall (b:Bool) (mapL:E→ F) (σ : A→+* B) : Score E A → Score F B → Prop
| atom {p : E→ A}{q : F→B}{v:Optical E}{w:Optical F} (hp : ∀ i,q (mapL i)=σ (p i))(hs : Alike b mapL v w): Recall b mapL σ (p ⊗ₜ[ℂ] v) (q ⊗ₜ[ℂ] w)
| plus {p q u v} : Recall b mapL σ p u → Recall b mapL σ q v → Recall b mapL σ (p+q) (u+v)
| zero : Recall b mapL σ 0 0

def Conforms (b:Bool)(σ : A→+* B) : Prop:= ∀ c : ℂ,∀ x, σ (c • x)= (realChange b c) • σ x
namespace Recall
variable {α : E→F}{X : Score E A}{Y : Score F B}
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
lemma unitRecall : Recall b α σ 1 1:= Recall.atom (v:=1) (w:=1) (p:=1) (q:=1) (fun _=> (map_one _).symm) (fun _ _ h=> h)
lemma illumination (p: Optical E)(q:Optical F)(h : Alike b α p q) : Recall b α σ (instructionScore E A p) (instructionScore F B q):= Recall.atom (fun _=> (map_one _).symm) h
lemma multiply {x y}(h : Recall b α σ X Y)(k : Recall b α σ x y): Recall b α σ (X*x) (Y*y):= by
    induction h with
    | zero => simp only [zero_mul]; exact .zero
    | plus _ _ hx hy=> rw [add_mul,add_mul]; exact .plus hx hy
    | @atom p q v w hp hv=>
      induction k with
      | zero=> simp only [mul_zero]; exact .zero
      | plus _ _ hx hy=> rw [mul_add,mul_add]; exact .plus hx hy
      | @atom u l v' w' hu hk=> rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]; exact .atom (fun x=> by simp only [Pi.mul_apply,hu,hp,map_mul]) (hv.times hk)
lemma negation (h : Recall b α σ X Y) : Recall b α σ (-X) (-Y):= by
   induction h with
   | zero=> rw [neg_zero,neg_zero]; exact .zero
   | plus _ _ hx hy=> rw [neg_add,neg_add]; exact .plus hx hy
   | atom hp h=> rw [← TensorProduct.neg_tmul,← TensorProduct.neg_tmul]; exact .atom (fun x=> by simp only [Pi.neg_apply,hp,map_neg]) h
lemma sum {X : I → Score E A}{Y : I→ Score F B} (c:Finset I) (h : ∀ i∈c,Recall b α σ (X i) (Y i)): Recall b α σ (∑ i∈ c,X i) (∑ i∈ c,Y i):= by
    induction c using Finset.induction with
    | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact .zero
    | insert i c hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact .plus (h i (by simp)) (ih (fun j hj=> h _ (Finset.mem_insert_of_mem hj)))
lemma synopsis {X : I→ Score E A}{Y : I' → Score F B} (t:I↪ I')(c:Finset I)(h : ∀ i∈c,Recall b α σ (X i) (Y (t i))) (hh : (c:Set I).Pairwise (fun i j=> Commute (X i) (X j))) (hm : (↑(c.map t):Set I').Pairwise (fun i j=> Commute (Y i) (Y j))): Recall b α σ (product c X) (product (c.map t) Y):=by
   induction c using Finset.induction with
   | empty=> simp only [product_empty,Finset.map_empty]; exact unitRecall
   | insert i c hi ih=>
     rw [Finset.map_insert] at hm; have ht:= Finset.coe_subset.mpr (Finset.subset_insert i c); have he: t i∉ c.map t:= by simp [hi];
     rw [Finset.map_insert,product_insert X hi hh,product_insert Y he hm]; exact (h i (by simp)).multiply (ih (fun j hj=>h _ (Finset.mem_insert_of_mem hj)) (hh.mono ht) (hm.mono (Finset.coe_subset.mpr (Finset.subset_insert ..))))
lemma column {ψ:E→ A→ₗ[ℂ] A}{σ':F→ B→ₗ[ℂ] B} (h:Recall b α σ X Y)(hp: ∀ i t, σ (ψ i t)= σ' (α i) (σ t)): Recall b α σ (reshape ψ X) (reshape σ' Y) := by
   induction h with
   | zero=> rw [map_zero,map_zero]; exact .zero
   | plus _ _ hx hy=> rw [map_add,map_add]; exact .plus hx hy
   | atom ht hv=> rw [reshape_tape,reshape_tape]; exact .atom (fun i=>by rw [evaluates,evaluates,ht,hp]) hv
lemma fin (h: Recall b α σ X Y) (hσ:Conforms b σ) {p:SmoothTests E}{q:SmoothTests F}(hp:follows b α p q)(i:E): σ (action i p X)=action (α i) q Y:= by
   induction h with
   | zero=> simp
   | atom ht hv=> rw [action_tmul,action_tmul,hσ,ht, hv _ _ hp]
   | plus _ _ hx hy=> simp only [map_add,hx,hy]
end Recall
end YM.Contacts.Transport
