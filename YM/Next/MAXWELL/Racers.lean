import YM.Next.MAXWELL.Refract
import YM.Next.MAXWELL.Stabilizer


/-! # Vector defect through stress weight -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick Climb
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} (F : Labels.Frames G) {d : ℕ}

abbrev motor (t : Vector d (Model F)) (a : Axis) := brand F (t a).toLinearMap

lemma motor_turn {t : Vector d (Model F)} (v : t∈Colors (scheme F) (hierarchy F).spin d)
    (a : Axis) (s : Signed) {p : WickPol G} (hp : p∈shellSector G d) :
    reflectPol s.ortho (motor F t a p) = tilt s a • motor F t (s.perm a) (reflectPol s.ortho p) := by
  let x := wrap F hp
  have ht : address F d x=p := shed F _
  rw [← ht,motor,brand_eval,← address_motion F (H:=(hierarchy F).spin),← address_motion F (H:=(hierarchy F).spin),motor,brand_eval]
  obtain ⟨A,B,D⟩ := v
  change address F _ ((Model F).mirror _ _ s (t a x))=_; rw [B,map_sum]
  rw [Finset.sum_eq_single_of_mem (s.perm a) (Finset.mem_univ _),map_smul,Signed.matrix_at,if_pos rfl]
  exact volumes _ _
  intro i _ hi; rw [Signed.matrix_at,if_neg (Ne.symm hi)]; simp

lemma motor_inverse {t : Vector d (Model F)} (v : t∈Colors (scheme F) (hierarchy F).spin d)
    (a : Axis) {p : WickPol G} (hp : p∈shellSector G d) :
    reflectPol oppositeFrame.ortho (motor F t a p) = -(motor F t a (reflectPol oppositeFrame.ortho p)) := by
  rw [motor_turn F v a _ hp]; simp [tilt,oppositeFrame]

lemma motor_low {t : Vector d (Model F)} (h : G.Simple) (hd : 4≤d) (v : t∈Colors (scheme F) (hierarchy F).spin d)
    (a : Axis) {p : WickPol G} (hp : p∈shellSector G 4) : motor F t a p ∈ Teams G 0 1 := by
  have hh : motor F t a p∈shellSector G 5 := by
    let x := wrap F hp
    let k := (scheme F).rise hd
    have he : address F d (k x)=p := by rw [address_rise,shed]
    obtain ⟨A,B,D⟩ := v
    rw [← he,motor,brand_eval]
    obtain ⟨y,hy⟩ := (A a).2 4 hd x
    change address F (d+1) (t a (k x))∈_
    change _ = t a (k x) at hy; rw [← hy,address_rise]; exact address_in F 5 y
  have hr := motor_inverse F v a (chain hd hp)
  rw [picture_zero h p hp] at hr
  rw [five_support h,Submodule.mem_sup] at hh
  obtain ⟨x,hx,y,hy,hK⟩ := hh
  rw [← hK,map_add,picture_zero h x hx,picture_five _ hy,neg_add] at hr
  have hh := add_right_cancel hr
  rw [← hK,show x=0 from ?_,zero_add]; assumption
  apply (smul_right_injective _ (by norm_num : (2:ℂ) ≠ 0))
  change (2:ℂ) • x=(2:ℂ) • (0:_)
  rw [smul_zero,two_smul]; nth_rw 1 [hh]; simp

section coast
variable (h : G.Simple) (t : Vector d (Model F)) (v : t∈ Colors (scheme F) (hierarchy F).spin d)
include h v
lemma racer (hd : 4≤d) (W : ∀ a, silence G d (motor F t a)) :
    ∃ b : ℝ, ∀ a,∀ p∈shellSector G 4, motor F t a p = b • rewired (glide G (basis a)) p := by
  let c := coreColor h
  have hx (a) : ∀ p : Flavor 0,∃ D : Panels 0 1, canopy G 0 1 D=(motor F t a) (team G p p) := by
    intro p
    have hp := team_label (d:=4) (G:=G) p p le_rfl
    apply tent _ (motor_low F h hd v a hp)
    let q := wrap F (chain hd hp)
    have he : address F d q=team G p p := shed F _
    nth_rw 1 [← he,motor,brand_eval]
    obtain ⟨A,B,C⟩ := v
    rw [← address_star F (H:=(hierarchy F).spin)];
    change address F (d+1) ((Model F).conj _ _ (t a q))=_
    rw [C,show address F _ (t a _) = _ from (brand_eval F (t a).toLinearMap _).symm,address_star,he, realTeam]
  choose f hf ht using fun a => receives c (W a) hd (hx a)
  have he : Conveyor f := by
    intro a s p
    by_cases hw:p=0
    · subst p; simp
    have hk := motor_turn F v a s (chain hd (team_label (d:=4) (G:=G) p p le_rfl))
    rw [orient_team,hf,hf,orient_team] at hk
    let i := actFlavor s.ortho 0 p
    have hi : i ≠ 0 := fun ha => hw (by rw [← act_inv_f s.ortho⁻¹ p,inv_inv, show actFlavor s.ortho 0 p=0 from ha,map_zero])
    obtain ⟨x,hx⟩ : ∃ x,i x≠0 := by by_contra! H; exact hi (LinearMap.ext H)
    let u := actFlavor s.ortho 1 ((f a) p)
    have hm : monoT i u=tilt s a • monoT i (f (s.perm a) i) := by
      apply canopy_faithful c (by decide); rw [map_smul,shelter,shelter]; exact hk
    apply smul_right_injective (Flavor 1) hx; change i x • u=i x • tilt s a • _; rw [smul_comm]
    exact LinearMap.congr_fun hm x
  obtain ⟨a,ha⟩ := classification f he c (ht 0)
  let k := a/2
  refine ⟨k,fun b p hp => ?_⟩
  let L := (rewired (glide G (basis b))).toLinearMap
  let K := LinearMap.eqLocus (motor F t b) ((k:ℂ) • L)
  suffices hv : shellSector G 4 ≤ K by
    rw [← volumes _ k]; exact hv hp
  rw [low_support h]; refine sup_le ?_ ?_
  · rw [BottomOnly,Submodule.span_le]; rintro x hx; obtain rfl : x=(1:WickPol G) := hx
    change motor F t b 1=(k:ℂ) • L 1
    obtain ⟨A,B,C⟩ := v
    conv_lhs => arg 2; rw [← unit_address F d]
    rw [motor,brand_eval,show (t b).toLinearMap ((Model F).unit d)=0 from (A b).1,map_zero,show L 1=0 from Derivation.map_one_eq_zero _,smul_zero]
  have hr (p : Flavor 0) : team G p p∈ K := by
    let r := feed (basis b) 0 p
    change motor F t b (team G p p)= (k:ℂ) • rewired (glide G (basis b)) (team G p p)
    rw [hf,ha,LinearMap.smul_apply,team_feed]
    change duetL G 0 1 p (a • r)=(k:ℂ) • (2:ℝ) • duetL G 0 1 p r
    rw [map_smul, volumes,smul_smul]; congr 1; unfold k; ring
  rw [Teams,Submodule.span_le]; rintro p ⟨x,y,rfl⟩
  have hv : Submodule.span ℂ (range fun x : Flavor 0 => team G x x) ≤ K := by
    rw [Submodule.span_le]; rintro p ⟨x,rfl⟩; exact hr x
  exact hv (team_square_span x y)
end coast
end YM.Maxwell.Free
