import YM.Pert.Rigid.Pallet
/-! Infinitesimal signed-equivariant field maps have symmetric coefficient matrix on quadratic slots. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Rigid
open Extra.FD RawLabels Function Maxwell Position UVNext.FreeStress Labels Set
open scoped Topology BigOperators
variable {G : Gauge} (F : Frames G)

lemma dispatch_cmul {d : ℕ} (B : Buffer F d) (c : ℂ) (v : E F d) : B.val (c • v)=c • B.val v := by
  have h (y : E F d) : c • y = c.re • y + c.im • Complex.I • y := by
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) c.re,RCLike.real_smul_eq_coe_smul (K:=ℂ) c.im, smul_smul,←add_smul]; congr 1
    exact c.re_add_im.symm
  rw [h, map_add, map_smul, map_smul, h (B.val v), B.property.2.2.2.2]

lemma wear_bij {d : ℕ} (s : Signed) : Function.Injective (wear F d s) := by
  intro x y h
  have he (v : E F d) : wear F d s⁻¹ (wear F d s v) = v := by rw [wear,wear,← Table.mirror_mul,inv_mul_cancel,Table.mirror_one]
  exact (he x).symm.trans ((congr_arg _ h).trans (he y))

lemma wear_ride {d : ℕ} (s : Signed) (p : E F d) : wear F d s p=rideO F s.ortho d p := by
  have ht : Injective (physicalLabel F d) := fun _ _ he=> (physical_round F _).symm.trans ((congr_arg (enroll F d) he).trans (physical_round F _))
  apply ht
  nth_rw 1 [← physical_round F p]
  rw [wear, enroll, mirror_embed, ← enroll, embed_round,← fixed_ortho, physical_ortho]
  exact congr_arg _ (Subtype.ext (flat_idem _))
lemma owner (B : Buffer F 4) (s : Signed) (p : E F 4) : wear F 4 s (B.val p)=B.val (wear F 4 s p) := by simp only [wear_ride, B.property.2.2.2.1]

lemma star_nonzero (h : G.Simple) (c : Option Face) : star F c ≠ 0 := fun he => by
  have hh := separates F h c c
  rw [if_pos rfl, show embed F 4 (sectors c) = 0 from he, map_zero] at hh
  exact zero_ne_one hh
lemma star_same (h : G.Simple) (c d : Option Face) (a b:ℂ) (ha : a≠0) (hh : a• star F c=b • star F d) : c=d := by
  have hh := congrArg (portLine F c) hh
  simp only [map_smul,star,separates F h,if_true,smul_eq_mul,mul_one] at hh
  by_contra hg; simp [hg] at hh; exact ha hh

lemma rotor (h : G.Simple) (c d : Option Face) (s : Signed) (a : ℂ) (ha : a*a=1) (hc : wear F 4 s (star F c)=a•star F d) (v : E F 4) :
    portLine F d (wear F 4 s v) = a * portLine F c v := by
  have hr q : portLine F d (wear F 4 s (star F q)) = a * portLine F c (star F q) := by
    rcases eq_or_ne q c with rfl|hh
    · rw [hc,map_smul,star,separates F h]; change _ = a * portLine F q (star F q);rw [star,separates F h]; simp
    obtain ⟨k,b,hb,ht⟩ := wearer F s q
    have hk : k ≠ d := by
      intro he;subst k
      have hx : b • star F c = a • star F q := by apply wear_bij F s; rw [map_smul, map_smul, hc, ht, smul_comm]
      have he := star_same F h _ _ b a (by rintro rfl; simp at hb) hx
      exact hh he.symm
    rw [ht,map_smul,star,separates F h, if_neg (Ne.symm hk),smul_zero]
    change 0=a*portLine F c (star F q); rw [star, separates F h,if_neg (Ne.symm hh), mul_zero]
  conv_lhs=>rw [← (stand F h).sum_equivFun v]
  simp_rw [map_sum,map_smul,basis_eq,hr,smul_eq_mul]
  conv_rhs=>rhs; rw [←(stand F h).sum_equivFun v]
  rw [map_sum,Finset.mul_sum]; simp_rw [map_smul,basis_eq,smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _=>mul_left_comm .. -- adjust above

def coeff (B : Buffer F 4) (c d : Option Face) := portLine F c (B.val (star F d))
lemma orient_transfer (h : G.Simple) {c d c' d' : Option Face} (s : Signed) {a b : ℂ} (ha : a*a=1) (_ : b*b=1) (hc : wear F 4 s (star F c)=a • star F c') (hd : wear F 4 s (star F d)=b • star F d') (B : Buffer F 4) : a * coeff F B c d = b * coeff F B c' d' := by
  unfold coeff
  rw [←rotor F h c c' s a ha hc,owner,hd,dispatch_cmul,map_smul,smul_eq_mul]
lemma unpaint (h : G.Simple) {c d : Face} (hh : paint (tape c) ≠ paint (tape d)) (B : Buffer F 4) : coeff F B (some c) (some d)=0 := by
  obtain ⟨i,hi⟩ := flavor_equal hh
  let t := orient_transfer F h (Signed.mirror i) (flavor_twice i (tape c)) (flavor_twice i (tape d)) (c:=some c) (c':=some c) (draw_mask F c i) (d:=some d) (d':=some d) (draw_mask F d i) B
  have hg : (flavor i (tape c)-flavor i (tape d)) * coeff F B (some c) (some d)=0 := by rw [sub_mul]; exact sub_eq_zero.mpr t
  exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr hi)
private lemma back (i) (c : Face) : mapSlate (swings i) (mapSlate (swings i) (tape c)) = tape c := by unfold mapSlate mapEdge; simp only [swingTest]
set_option maxHeartbeats 2200000 in
lemma reflect_path (h : G.Simple) {c d : Face} (hp : paint (tape c) = paint (tape d)) (B : Buffer F 4) : coeff F B (some d) (some c) = coeff F B (some c) (some d) := by
  obtain ⟨i,hc,hd⟩ := (havePath c d hp).1
  let s := plain (swings i)
  have move (e) : wear F 4 s (star F (some e)) = draw F (mapSlate (swings i) (tape e)) := by rw [coincides]; exact draw_roll F _ _
  obtain ⟨a,ha,hx⟩ := sign_match F _ _ hc
  obtain ⟨b,hb,hy⟩ := sign_match F _ _ hd
  replace hx : wear F 4 s (star F (some c)) = a • star F (some d) := (move _).trans (hx.trans (congr_arg (a • ·) (coincides F d).symm))
  replace hy : wear F 4 s (star F (some d)) = b • star F (some c) := (move _).trans (hy.trans (congr_arg (b • ·) (coincides F c).symm))
  have hn : a≠0 := by rintro rfl;simp at ha
  have he : (a*b) • star F (some c) = star F (some c) := by
    rw [mul_smul, ← hy, ←map_smul,←hx,coincides,draw_roll,draw_roll,back]
  have he := congrArg (portLine F (some c)) he; simp only [map_smul, star, separates F h,if_true,smul_eq_mul,mul_one] at he -- replace
  have ht : a=b := mul_left_cancel₀ hn (ha.trans he.symm)
  rw [← ht] at hy
  exact (mul_left_cancel₀ hn (orient_transfer F h s ha ha hx hy B)).symm

end YM.Pert.Rigid
