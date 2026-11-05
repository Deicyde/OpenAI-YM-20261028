import YM.Bid.Craft
import YM.Next.MAXWELL.Depth
import YM.Next.MAXWELL.Flavor

/-!
# Three low legs

Obtain explicitly the triangular identity and the cluster power -5,
with sign. Needed in real-vector testing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j l d n : ℕ}

abbrev tripod (x y z : E4) : Points 3 := Points.cons x (pairPoints y z)

def triangle (G : Gauge) (x y z : E4) : WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] ℂ where
  toFun a :=
    { toFun b := (((moment G (tripod x y z)).curryLeft a).curryLeft b).toLinearMap (fun _ => 0) 0
      map_add' b c := by apply LinearMap.ext; intro u; simp
      map_smul' t b := by apply LinearMap.ext; intro u; simp }
  map_add' a b := by apply LinearMap.ext; intro c; apply LinearMap.ext; intro u; simp
  map_smul' a b := by apply LinearMap.ext; intro c; apply LinearMap.ext; intro u; simp

def triCols (a b c : WickPol G) : Fin 3 → WickPol G := Fin.cons a (Fin.cons b fun _ => c)
lemma tri_eval (x y z : E4) (a b c : WickPol G) : triangle G x y z a b c = moment G (tripod x y z) (triCols a b c) := by
  simp only [triangle, LinearMap.coe_mk, AddHom.coe_mk,MultilinearMap.toLinearMap_apply, MultilinearMap.curryLeft_apply]; congr 1
  ext1 i; fin_cases i <;> simp [triCols] ; rfl
lemma tri_ok {x y z : E4} (h : x≠y) (w : x≠z) (r : y≠z) : tripod x y z∈conf _ := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [Points.cons,tripod,pairPoints,h,h.symm] <;> (first | exact w | exact w.symm | exact r | exact r.symm)
lemma tri_around {x y z : E4} (h : tripod x y z∈conf 3) (a b c : WickPol G) : triangle G x y z a b c = triangle G y x z b a c := by
  let s := Equiv.swap (0:Fin 3) 1
  rw [tri_eval,exchangeSites s h, tri_eval]
  have hs : Points.rearrange s (tripod x y z)=tripod y x z := by
    ext1 i; fin_cases i <;> simp [s] <;> rfl
  change (moment G (Points.rearrange s (tripod x y z))) _ = _
  rw [hs]; congr 1
  ext1 i; fin_cases i <;> simp [s] <;> rfl
lemma tri_switch {x y z : E4} (h : tripod x y z∈conf 3) (a b c : WickPol G) : triangle G x y z a b c = triangle G z y x c b a := by
  let s := Equiv.swap (0:Fin 3) 2
  rw [tri_eval,exchangeSites s h, tri_eval]
  have hs : Points.rearrange s (tripod x y z)=tripod z y x := by
    ext1 i; fin_cases i <;> simp [s] <;> rfl
  change (moment G (Points.rearrange s (tripod x y z))) _ = _
  rw [hs]; congr 1
  ext1 i; fin_cases i <;> simp [s] <;> rfl

lemma triangle_stat {x y z : E4} (h : tripod x y z∈conf 3) {T : Module.End ℂ (WickPol G)} (H : silence G d T) {p q r}
    (hp : p ∈ shellSector G d) (hq : q ∈ shellSector G d) (hr : r ∈ shellSector G d) :
    triangle G x y z (T p) q r + triangle G x y z p (T q) r + triangle G x y z p q (T r) = 0 := by
  let V := triCols p q r
  have he := H 3 V _ (fun i => Fin.cases hp (Fin.cases hq (fun _ => hr)) i) h
  rw [Fin.sum_univ_three] at he; simp_rw [tri_eval];
  rw [show triCols (T p) q r = update V 0 (T (V 0)) from (Fin.update_cons_zero ..).symm,
    show triCols p (T q) r=update V 1 (T (V 1)) from ?_,
    show triCols p q (T r)=update V 2 (T (V 2)) from ?_]; exact he
  all_goals ext1 i; fin_cases i <;> simp [triCols,V] ; rfl

section Signal
variable {x y z : E4} (h₁ : x≠y) (h₂ : x≠z) (h₃ : y≠z)
include h₁ h₂ h₃

theorem tri_cost (p q u w : Factor G) : triangle G x y z (letter p*letter q) (letter u * letter u) (letter w*letter w) =
    4 * (linkEntry (x,p) (y,u)*linkEntry (x,q) (z,w) + linkEntry (x,p) (z,w)*linkEntry (x,q) (y,u)) *
       linkEntry (y,u) (z,w) := by
  let f : Fin 2 → Factor G := Fin.cons u fun _ => w
  let A := [(0 : Fin 2),0,1,1]
  let B := Fin.cons (α:=fun _ : Fin 2 => WickPol G) (letter u* letter u) (fun _ => letter w*letter w)
  rw [tri_eval]; change moment G _ (Fin.cons _ B) = _
  have he : B=bag id f A := by
    ext1 i; fin_cases i <;> simp [B,A,bag,f]
  change moment G (Points.cons x (pairPoints y z)) _ = _
  rw [he,show letter p * letter q = ([p,q].map letter).prod by simp,planted _ _ _ _ _ (tri_ok h₁ h₂ h₃)]
  change pairCost _ ([(x,p),(x,q),(y,u),(y,u),(z,w),(z,w)])=_
  simp only [pair_step,pulls_cons,pulls_nil,zero_mul,mul_zero,add_zero,zero_add,link_zero]
  rw [pairCost]; ring

theorem tri_fares (a : Flavor 0) (v : Flavor 1) (p q : Flavor 0) (c : G.ColorIndex) :
    triangle G x y z (team G a v) (team G p p) (team G q q) = ((G.lieDim : ℝ)*4*
      (fare c a p (x-y)*fare c v q (x-z) + fare c a q (x-z)*fare c v p (x-y)) * fare c p q (y-z):ℝ) := by
  let F {j : ℕ} (a : Flavor j) (i : G.ColorIndex) : Factor G := ⟨j,flavor j i a⟩
  have he {j l : ℕ} (a : Flavor j) (p : Flavor l) {x y : E4} (h : x≠y) (i m) :
      linkEntry (x,F a i) (y,F p m) = (((if i=m then 1 else 0) * fare c a p (x-y):ℝ) : ℂ) := by
    rw [link_eq x y _ _ h]; exact congr_arg ((↑) : ℝ → ℂ) (any_ink c a p _ _ (sub_ne_zero.mpr h))
  unfold team; simp only [map_sum,LinearMap.sum_apply];
  have hl (i m l : G.ColorIndex) := tri_cost h₁ h₂ h₃ (F a i) (F v i) (F p m) (F q l)
  change (∑ l : G.ColorIndex, ∑ m : G.ColorIndex, ∑ i : G.ColorIndex, triangle G x y z (letter (F a i) * letter (F v i)) (letter (F p m) * letter (F p m)) (letter (F q l) * letter (F q l)))=_
  simp_rw [hl, he _ _ h₁, he _ _ h₂, he _ _ h₃]
  let k := (fare c a p (x-y)*fare c v q (x-z) + fare c a q (x-z)*fare c v p (x-y))*fare c p q (y-z)
  rw [show (↑((G.lieDim:ℝ) * 4 * _ * fare c p q (y-z)):ℂ)= ∑ _i : G.ColorIndex, ((4*k:ℝ):ℂ) from ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
      · simp [k]; ring
      intro m _ hm; simp [hm]
    intro m _ hm; refine Finset.sum_eq_zero fun l _ => ?_
    simp [hm]
  simp [k,Gauge.ColorIndex]; ring
end Signal
end YM.Maxwell.Free
