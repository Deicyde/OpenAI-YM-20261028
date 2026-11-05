import YM.Next.RANK.Terrain
import YM.Next.RANK.Tuning
import YM.Work.G02

/-! # Line norm budget for every edge of an origin patch -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Set Filter Lattice Wilson RG Beamer Source Labels Source.Drops
open scoped Matrix.Norms.Frobenius ContDiff Topology BigOperators

variable {G : Gauge} (H : Hol G) (d m : ℕ)
variable {n : Side}

private lemma starred {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →ₗᵢ[ℝ] V) (A : X → V)
    (n : ℕ) (h : ContDiffAt ℝ n A 0) : ContDiffAt ℝ n (L∘A) 0 ∧ slopeCap n (L∘A) 0=slopeCap n A 0 :=
  ⟨L.toContinuousLinearMap.contDiff.contDiffAt.comp _ h,L.norm_iteratedFDeriv_comp_left h le_rfl⟩

def hlink (e : Edge Cover) (i : Step) (J : Snap G d) : G.Mat :=
  let u:=H.links d (expand d J) 1 e
  if i.neg then G.mat u⁻¹ else G.mat u

lemma step_box {x : Cover} (d : Step) : (d.used x).1=x ∨ (d.used x).1=x+d.vec := by unfold Step.used Step.vec; cases d.neg <;> simp [sub_eq_add_neg]

-- root-frame list of matrices, all within set. Account each endpoint.
def lace (x : Cover) : Walk → List (Snap G d→G.Mat)
  | []=>[]
  | i::l => hlink H d (i.used x) i :: lace (x+i.vec) l

local notation "live" => fun H d J => Hol.links H d (expand d J) 1
lemma lace_prod (x : Cover) (l : Walk) : (lace H d x l).prod=fun J=>G.mat (travel (live H d J) x l) := by
  induction l generalizing x with
  | nil => ext1 i; simp [lace,travel]
  | cons a l ih =>
    rw [lace,List.prod_cons,ih]; funext i; rw [travel,Gauge.mat_mul]; unfold hlink; simp only [Pi.mul_apply,Step.read]; split <;> rfl
lemma laces (l : Walk) (x) : (lace H d x l).length=l.length := by induction l generalizing x with | nil => rfl | cons i l ih => simp [lace,ih]

def rock (u : UsedEdges (box m)) (J : Snap G d) : G.Mat := G.mat (central (live H d J) u.val)
def bore (u : UsedEdges (box m)) : Snap G d→G.Color := G.plog∘rock H d m u

-- a third piece for inverse of final factors; list through reversals, membership transport easy.
def woods (u : UsedEdges (box m)) : List (Snap G d→G.Mat) :=
  let x:= u.val.1; let y:= x+step u.val.2
  let w := lace H d 0 (paths y)
  lace H d 0 (paths x) ++ [hlink H d u.val (posDir u.val.2)] ++ w.reverse.map fun v => fun i => star (v i)
lemma taken (u : UsedEdges (box m)) : (woods H d m u).prod=rock H d m u := by
  have he (p : List (Snap G d→G.Mat)) : (p.reverse.map fun v => fun i => star (v i)).prod=fun x=> star (p.prod x) := by
    induction p with
    | nil => ext1 i; simp
    | cons a l ih =>
      rw [List.reverse_cons,List.map_append,List.prod_append,ih]
      funext i; simp
  unfold woods; simp only [List.prod_append,he,lace_prod]; ext1 i; simp only [Pi.mul_apply,rock,central,leaves,Gauge.mat_mul,Gauge.mat_inv,Lattice.gauge,List.prod_cons,List.prod_nil,mul_one]; rfl
@[simp] lemma unroll {b : ℕ} (u : UsedEdges (box b)) : rock H d b u 0=1 := by
  unfold rock; rw [show live H d 0=1 from funext fun i=> (Work.G02.linkGerm H d i).2.1]; change G.mat (travel 1 _ _ * 1 * (travel (1 : CoverConfig G) _ _)⁻¹)=_; simp only [Pressure.one,inv_one, mul_one,G.mat_one]
private lemma star_rock (F : Snap G d→G.Mat) (h : ContDiffAt ℝ m F 0) : ContDiffAt ℝ m (fun x => star (F x)) 0 ∧ slopeCap m (fun x=> star (F x)) 0=slopeCap m F 0 := by
  let A : G.Mat→ₗᵢ[ℝ] G.Mat := { __ := (starL' ℝ (A:=G.Mat)).toLinearEquiv.toLinearMap, norm_map' U := by change ‖star U‖=‖U‖; apply norm_star }
  exact starred A F m h

private lemma optics (H : Hol G) (d n : ℕ) : ∃ c : ℝ, ∃ R : ℕ, 1≤c ∧ ∀ b : ℕ, ∀ u : Edge Cover, u.1∈box b → ∀ i : Step,
    let F := hlink H d u i
    ContDiffAt ℝ n F 0 ∧ F 0=1 ∧ ∀ j, j≤n → slopeCap j F 0 ≤ c*(1+(b:ℝ))^R := by
  choose C r hc h using fun j => windage H d j
  obtain ⟨c,R,hy,Hc⟩ := artillery C r n hc
  refine ⟨max 1 c,R,le_max_left ..,fun b u hb i => ?_⟩
  let F:= fun J=> G.mat (live H d J u)
  have ha : ContDiffAt ℝ n F 0 := (h n b u hb).1.contDiffAt
  have hp {j : ℕ} (hj : j≤n) : slopeCap j F 0≤ max 1 c*(1+(b:ℝ))^R := ((h j b u hb).2.trans
    (Hc _ (by simp) j hj)).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
  have hz : F 0=1 := by dsimp only [F]; rw [(Work.G02.linkGerm H d u).2.1,G.mat_one]
  dsimp only
  unfold hlink; split
  · simp_rw [Gauge.mat_inv]
    exact ⟨(star_rock d _ F ha).1, show _ from (congr_arg star hz).trans (by simp),fun j hj => ((star_rock d _ F (ha.of_le (by exact_mod_cast hj) : ContDiffAt ℝ j F 0)).2).trans_le (hp hj)⟩
  exact ⟨ha,hz,fun j hj=>hp hj⟩

private lemma treetops (H : Hol G) (d m : ℕ) : ∃ C : ℝ,∃ v : ℕ,1≤C∧ ∀ b : ℕ, ∀ u : UsedEdges (box b),
    ContDiffAt ℝ m (rock H d b u) 0 ∧ ∀ i,i ≤ m→ slopeCap i (rock H d b u) 0≤ C*(1+(b:ℝ))^v := by
  obtain ⟨c,R,hc,Hc⟩ := optics H d m
  obtain ⟨L,v,hL,hl⟩ := conquer G.Mat (Snap G d) m
  let T := fun (b : ℕ) => c * (1+(b:ℝ))^R
  refine ⟨max 1 (L*(8*c)^v),(R+1)*v, le_max_left ..,fun b u=>?_⟩
  let a:= T b
  let x:=u.val.1; let y:= x+step u.val.2
  have hx : x∈ box b := u.property.1; have hy : y∈box b := u.property.2
  let f (A : Snap G d→ G.Mat) := ContDiffAt ℝ m A 0 ∧ A 0=1 ∧ ∀ j,j≤m→slopeCap j A 0 ≤ a
  have he (p : Walk) (x : Cover) (h : ∀ z∈visits x p,z∈box b) : ∀ i∈lace H d x p, f i := by
    induction p generalizing x with
    | nil => simp [lace]
    | cons k l ih =>
      intro i hi; rcases List.mem_cons.mp (show i ∈ hlink H d (k.used x) k :: lace H d (x+k.vec) l from hi) with hi|hi
      · subst i; refine Hc b _ ?_ _
        rcases step_box (x:=x) k with he|he
        · rw [he]; exact h x List.mem_cons_self
        rw [he]; exact h _ (by cases l <;> simp [visits])
      apply ih (x+k.vec) (fun z hz=>h z (List.mem_cons_of_mem x hz)) _ hi
  let P:= woods H d b u
  have h (i) (hi : i∈P) : f i := by
    obtain (h|h)|h := Or.imp_left List.mem_append.mp (List.mem_append.mp hi)
    · exact he _ _ (village _ hx) _ h
    · rw [List.mem_singleton.mp h]; exact Hc _ _ hx _
    obtain ⟨i,hv,rfl⟩ := List.mem_map.mp h; obtain ⟨h,hx,hc⟩ := he _ _ (village _ hy) i (List.mem_reverse.mp hv)
    refine ⟨(star_rock d _ i h).1,?_,fun j hj=> (star_rock d j i (h.of_le (by exact_mod_cast hj))).2.trans_le (hc j hj)⟩
    exact (congr_arg star hx).trans (by simp)
  have hT : 1≤a := one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ (by simp))
  obtain ⟨hp,-,hs⟩ := hl P 0 a hT h
  rw [← taken]; refine ⟨hp,fun i hi=> (hs i hi).trans ?_⟩
  let s:=1+(b:ℝ)
  have hz : P.length ≤ 8*b+1 := by
    have hh : (paths x).length≤4*b := (lengths _).trans_le (bounded hx)
    have hl : (paths y).length ≤4*b := (lengths _).trans_le (bounded hy)
    unfold P woods; simp only [List.length_append,laces,List.length_cons,List.length_nil,List.length_map,List.length_reverse]
    change (paths x).length+ (0+1)+(paths y).length≤_; omega
  have hv : (1+(P.length:ℝ))*a ≤ 8*c*s^(R+1) := by
    have he : (1+(P.length:ℝ)) ≤ 8*s := by
      have ht : (P.length:ℝ) ≤ 8*(b:ℝ)+1 := by exact_mod_cast hz
      unfold s; linarith only [ht]
    refine (mul_le_mul_of_nonneg_right he (zero_le_one.trans hT)).trans_eq ?_
    unfold a T s; ring
  have he : (1+(P.length:ℝ))*a≥0 := by positivity
  change L*((1+↑P.length) * a)^v ≤ _
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he hv _) hL).trans
  change _ ≤ max _ _ * s^_
  rw [mul_pow, ← pow_mul, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (by unfold s; positivity)

-- derivative on log axial loop. Cost through order m independent of b except
-- polynomial. Gives also necessary germs.
lemma slope_pos {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) (A : E → F) (x) : 0≤slopeCap n A x := norm_nonneg _
lemma shots (H : Hol G) (d m : ℕ) : ∃ C : ℝ,∃ v : ℕ, 0 ≤ C ∧ ∀ b : ℕ, ∀ u : UsedEdges (box b),
    let F:= bore H d b u
    ContDiffAt ℝ m F 0 ∧ slopeCap m F 0 ≤ C*(1+(b:ℝ))^v := by
  obtain ⟨C,v,hc,Hc⟩ := treetops H d m
  let T i := slopeCap i G.plog 1
  let L:= ∑ i∈Finset.range (m+1), T i
  have hL : ∀ i,T i≥0 := fun i=> slope_pos ..
  have hp : L≥0 := Finset.sum_nonneg fun _ _ => hL _
  refine ⟨m.factorial * L * C^m,v*m,by positivity,fun b u => ?_⟩
  let R:= rock H d b u
  have hv : R 0=1 := unroll ..
  have hs : ContDiffAt ℝ m G.plog (R 0) := hv ▸ G.plog_diff.of_le le_top
  have hz := Hc b u
  let t:= C*(1+(b:ℝ))^v
  have ht : 1≤t := one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ (by simp))
  refine ⟨hs.comp 0 hz.1,(strap R G.plog 0 m hz.1 hs L t (fun i hi=> hv.symm ▸ Finset.single_le_sum (fun i _ => hL i) (show i∈Finset.range (m+1) from Finset.mem_range.mpr (by omega)))
    (fun i hi hm => (hz.2 i hm).trans (show t ≤ t^i by nth_rw 1 [← pow_one t]; exact pow_le_pow_right₀ ht hi))).trans_eq ?_⟩
  unfold t; rw [mul_pow,pow_mul,mul_assoc]; ring
end YM.Next.Rank.Spindle
