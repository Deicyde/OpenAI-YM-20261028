import YM.Next.SCHEDULE.GridCost

/-!
# Threshold and path-length receipt for an incoming slot

Actual probe with rooted projection; require Healthy at its true references,
price directions from anchor o. Include any orientation or inverse-path by
using its Walk. This lemma can be used also on short terms in long-path
square tails, not asserting nearest paths continue to represent anything
else. Numbers uniform even balls bigger than side and P,k large (constant
at those orders).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Wages
open Work.G07 Lattice RG Wilson
open scoped ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side}
namespace Path

def single (x : Site n) (a : Step) : Piece G n := if a.neg then .pull (a.used x) else .push (a.used x)

def tissue (x : Site n) : Walk → Trail G n
  | [] => []
  | a::l => single x a::tissue (x+a.vec) l

theorem picture (x : Site n) (l : Walk) (U : Config G n) :
    G.mat (travel U x l)=eval (tissue x l) U := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    cases a with | mk i c => cases c <;> simp [travel,tissue,eval,Step.read,single,Piece.call,ih]

private lemma one_walk (x : Site n) (a : Step) : separation x (x+a.vec) ≤ 1 := by
  rw [separation_comm,separation, add_comm,add_sub_cancel_right, Step.vec]; split
  · rw [pdist_neg]; exact pdist_step _
  exact pdist_step _

private theorem sieve (x : Site n) (l : Walk) :
    price (tissue (G:=G) x l)=1 ∧ (uses (tissue (G:=G) x l)).length=l.length ∧
      ∀ i∈uses (tissue (G:=G) x l),separation x i.1 ≤ l.length := by
  induction l generalizing x with
  | nil => simp [tissue,price,uses]
  | cons a l ih =>
    obtain ⟨h,h',he⟩:=ih (x+a.vec)
    have hx : (single (G:=G) x a).size=1 ∧ (single (G:=G) x a).links = [a.used x] := by
      unfold single; split <;> exact ⟨rfl,rfl⟩
    have ha:= one_walk x a
    rw [tissue,price,h,hx.1, one_mul,uses,hx.2]
    simp only [List.singleton_append,List.length_cons,h']
    refine ⟨trivial,trivial,fun i hi => ?_⟩; rcases List.mem_cons.mp hi with rfl|hg
    · cases a with
      | mk i b =>
        cases b
        · rw [show (Step.used _ _).1=x from rfl]; simp
        apply le_trans (b:=1) _ (Nat.le_add_left ..)
        simpa [Step.vec,Step.used,sub_eq_add_neg] using ha
    exact le_trans (separation_triangle x (x+a.vec) i.1) (by have := he i hg; omega)
end Path

/-- Slot as a single group word fed into projection -- no path exponential
lost to Frobenius norms. -/
def detour (a : Slot) :=
    a.walk ++ square a.plaq.val.1 a.plaq.val.2 ++ Lattice.reverse a.walk

def projector (G : Gauge) : G.Mat →L[ℝ] G.Color :=
    G.projectColor.toContinuousLinearMap.comp ((1/2:ℝ) • (ContinuousLinearMap.id ℝ _ - (starL' ℝ).toContinuousLinearMap))

lemma hangs (s : Slot) (p : Site n) (U : Config G n) :
    s.atSite U p= projector G (Path.eval (Path.tissue p (detour s)) U) := by
  have hv : projector G (G.mat (travel (expandAt p U) 0 (detour s))) = s.atSite U p := by
    let F := expandAt p U
    have h : travel F 0 (detour s) = travel F 0 s.walk * faceValue F (s.offset,s.plaq) * (travel F 0 s.walk)⁻¹ := by
      rw [detour,travel_append,travel_append,stop_append,square_stop,travel_reverse]
      rfl
    rw [show travel _ 0 _= travel F _ (detour s) from rfl,h]
    change G.curvature _=_
    rw [G.curvature_conjugate]; rfl
  rw [travel_at,map_zero,zero_add,Path.picture] at hv; exact hv.symm

lemma norm_projector (G : Gauge) (A : G.Mat) : ‖projector G A‖ ≤ G.colorScale⁻¹*‖A‖ := by
  change ‖G.projectColor ((1/2:ℝ) • (A-star A))‖ ≤ _
  apply (G.project_norm ..).trans
  have hA: ‖(1/2:ℝ) • (A-star A)‖ ≤ ‖A‖ := by
    rw [norm_smul]; have h:= norm_sub_le A (star A); rw [norm_star] at h; rw [Real.norm_of_nonneg (by positivity)]; linarith
  apply le_trans (div_le_div_of_nonneg_right hA G.colorScale_pos.le)
  rw [div_eq_mul_inv,mul_comm]

private lemma detour_length (s : Slot) : (detour s).length ≤ 2*s.length := by
  simp only [detour,Slot.length,square,Lattice.reverse,List.length_append,List.length_reverse,List.length_map,List.length_cons,List.length_nil]; omega

/-- enough even using detour positions; no t or L in the price. -/
def margin (G : Gauge) (P l : ℕ) := 2*(G.colorScale+1)*2^P*((l:ℝ)+1)^(P+1)
def slotCost (G : Gauge) (P k l : ℕ) := (1+G.colorScale⁻¹ * ‖(1:G.Mat)‖) * margin G P l^k

lemma margin_ge (G : Gauge) (P l : ℕ) : 1 ≤ margin G P l := by
  have hp:=G.colorScale_pos
  have ht : (1:ℝ) ≤ ((l:ℝ)+1)^(P+1):=one_le_pow₀ (by simp)
  have hy : (1:ℝ) ≤ 2^P:=one_le_pow₀ (by norm_num)
  unfold margin; refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hy) ht

lemma slot_ge (G : Gauge) (P k l : ℕ) : 1 ≤ slotCost G P k l := by
  have hp:=G.colorScale_pos
  unfold slotCost; refine one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (by positivity)) (one_le_pow₀ (margin_ge ..))

/-- `l` may be e.g. the grand length in an atom. -/
theorem slotPays (x : Slot) (S : Finset Cover) (hs : x.stencil ⊆ S) (l : ℕ) (hl : x.length ≤ l)
    (o : Site n) (b : BudgetPoint) :
    LeftBound b.order (b.dirBound o) (Healthy b.threshold (S.image fun x => wrap n x + o)) 1
       (slotCost G b.power b.order l * b.threshold) (fun U : Config G n => x.atSite U o) := by
  let f:=fun U : Config G n => x.atSite U o
  let w := Path.tissue (G:=G) o (detour x)
  have hF : f=fun U => projector G (Path.eval w U):=funext (hangs x o)
  have hE : LeftSmooth b.order f := hF.symm ▸ (Path.soft w _).postcomp _
  have hp := b.threshold_pos.le
  let C := slotCost G b.power b.order l; have hh : 1≤C := slot_ge ..
  refine ⟨hE,mul_nonneg (zero_le_one.trans hh) hp,fun a ha hD U hU => ?_⟩
  simp only [one_pow,mul_one]
  by_cases ht : a=[]
  · subst a; exact (slot_bound x hs _ o U hU).trans (le_mul_of_one_le_left hp hh)
  change ‖leftDerivs f a U‖ ≤ C*b.threshold
  have ha' : leftDerivs (fun U => projector G (Path.eval w U)) a U=projector G (leftDerivs (Path.eval w) a U) :=
    congr_fun (left_linear (Path.soft w b.order) _ ha) U
  rw [hF,ha']
  apply le_trans (norm_projector G _)
  obtain ⟨h1,h2,h3⟩:=Path.sieve (G:=G) o (detour x)
  let T := G.colorScale*b.threshold*(1+(2:ℝ)*l)^b.power
  let N := margin G b.power l; have hn : 1≤N := margin_ge ..
  have hg:=G.colorScale_pos
  have he : 0 ≤ T := by unfold T; positivity
  have hd := (detour_length x).trans (Nat.mul_le_mul_left _ hl)
  have hc : T * (Path.uses w).length ≤ N*b.threshold := by
    have hw : ((Path.uses w).length : ℝ) ≤ 2*l := by
      unfold w; rw [h2]; exact_mod_cast hd
    calc
      T * (Path.uses w).length ≤ T*(2*l) := mul_le_mul_of_nonneg_left hw he
      _ ≤ (G.colorScale+1)*b.threshold*(2*((l:ℝ)+1))^b.power * (2*((l:ℝ)+1)) := by unfold T; gcongr <;> linarith
      _ = _ := by unfold N margin; rw [pow_succ,mul_pow]; ring
  have hT (i) (hi : i ∈ Path.uses w) (j : Directions G n) (hj : j∈a) : ‖G.colorMat (j i)‖ ≤ T := by
    have hx := (h3 _ hi).trans hd
    have he := hD _ hj i
    rw [G.colorMat_norm]; refine (mul_le_mul_of_nonneg_left he hg.le).trans ?_
    unfold T; rw [mul_assoc]; gcongr
    rw [separation_comm]; exact_mod_cast hx
  have hB := Path.bill w T he U a hT
  change _ ≤ C*b.threshold
  have hd : b.threshold^a.length ≤ b.threshold := by
    have hk : 1 ≤ a.length := List.length_pos_iff.mpr ht
    simpa only [pow_one] using pow_le_pow_of_le_one hp b.threshold_le hk
  calc
    _ ≤ G.colorScale⁻¹*((Path.price w*‖(1:G.Mat)‖)*(T*(Path.uses w).length)^a.length) := mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr G.colorScale_pos.le)
    _ ≤ G.colorScale⁻¹*((1*‖(1:G.Mat)‖)*(N*b.threshold)^a.length) := by
      have hx : Path.price w=1:= h1; rw [hx]; gcongr
    _ ≤ G.colorScale⁻¹*((1*‖(1:G.Mat)‖)*(N^b.order*b.threshold)) := by rw [mul_pow]; gcongr
    _ ≤ _ := by
      let L := b.order; change _ ≤ (1+G.colorScale⁻¹*‖(1:G.Mat)‖)*N^L*b.threshold
      have hN : 0 ≤ N^L*b.threshold:=mul_nonneg (pow_nonneg (zero_le_one.trans hn) L) hp
      unfold L at *; linarith
end YM.Next.Scheduling.Wages
