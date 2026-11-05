import YM.RG08.Rudder.Sym.Paint

/-!
# Symmetry-preserving stable lift. Also all scale choices independent of increasing
block factors. Rank two uses Loop.noPole; can meet from symmetries separately.
-/
noncomputable section
namespace YM.RG08.Rudder.Symmetry
open scoped Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Pert.Bulk Exterior Laurent AnalyticNext.QuarticMatch.BoxChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}[Fintype I]{n:ℕ}

structure Cloak (V:Submodule ℝ (Urn I n))(r:ℕ)(F:Raw I n):Prop where
 path : Cohort F
 field' : Graded F fun _=>r
 beam : Forms.Sym F
 firm : Cardinal F
 hair : hue V F

def polish (V:Submodule ℝ (Urn I n))(F:Raw I n):=bleach (canopy I n (applyHue (fix V) F))
omit [Fintype I] in
lemma polish_delivers(V:Submodule ℝ (Urn I n))(F:Raw I n){r:ℕ}(h:Graded F (fun _=> r))(hp:Cohort F)(hv:adjGrade V):Cloak V r (polish V F):=by
 let f:Raw I n:=canopy I n (applyHue (fix V) F)
 have he:polish V F=bleach f:=rfl
 rw [he];refine ⟨(canopy_cohort (applyHue_path hp)).clean,clean_field (canopy_field (applyHue_grade h)),symmetric _,cardinal_clean covered, bleach_hue hv (canopy_hue (fixed_hue _))⟩
omit [Fintype I] in
lemma polish_keeps(V:Submodule ℝ (Urn I n))(F:Raw I n){r:ℕ}(h:Cloak V r F): polish V F=F:=by rw [polish,hue_fixed _ h.hair,cardinal_fixed h.firm,bleached h.beam]
omit [Fintype I] in
lemma polish_picture (V:Submodule ℝ (Urn I n))(F:Raw I n)(h:Graded F 2):picture I n (polish V F)=polish V (picture I n F):=by rw [polish,polish,picture_clean,picture_canopy (canopyF (V:=V) h),picture_hue]
where
 canopyF {V:Submodule ℝ (Urn I n)}(h:Graded F 2):Graded (applyHue (fix V) F) 2:=applyHue_grade h

def endFee(V:Submodule ℝ (Urn I n))(σ:ℝ):ℝ:= debit' (Tone I) n σ*fixedFare (fix V)* Real.exp (8*(σ/2))
lemma finish_pos (V: Submodule ℝ (Urn I n))(σ:ℝ)(h:0<σ)(hn:0<n):0≤endFee V σ:=mul_nonneg (mul_nonneg (debit'_nn h hn) (fare_pos _)) (Real.exp_pos _).le
lemma bolster (V:Submodule ℝ (Urn I n))(F:Raw I n)(σ C:ℝ)(h:0<σ)(hc:0≤C)(hn:0<n)(hF:Cohort F)(hp:Held (carpet (Tone I)) σ C F): Held (carpet (Tone I)) (σ/2) (endFee V σ*C) (polish V F):=by
 have he:=canopy_held (hue_held (fix V) σ C h hc hn hF hp) (by positivity) (mul_nonneg (mul_nonneg (debit'_nn h hn) (fare_pos _)) hc)
 unfold endFee;rw [mul_right_comm];exact he.bleach (by have h1:=debit'_nn (I:=Tone I) h hn;have h2:=fare_pos (fix V); positivity)
omit [Fintype I] in
lemma polish_sub (V : Submodule ℝ (Urn I n))(F G:Raw I n):polish V (F-G)=polish V F-polish V G:=by simp only [polish,map_sub,bleach_sub]

/-- Align using this fixed map at every occurrence of this stage & arity. -/
def Lyapunov (V:Submodule ℝ (Urn I (n+1)))(α:ℝ)(F:Raw I (n+1)):= polish V (lineLift I n α F)

def FirstNull {n:ℕ} (F:Raw I (n+1)):Prop:= match n with
 | 1=>Loop.noPole F
 | _=>True

theorem base (σ:ℝ)(hσ:0<σ)(hn:1≤n): ∃ α Q:ℝ,0<α∧α≤σ∧0≤Q∧
   ∀ (F:Raw I (n+1)) (p:ℝ),0≤p→ Cohort F→Graded F 1→Closing F→FirstNull F→ Held (carpet (Tone I)) σ p F→
      let U:= lineLift I n α F
      picture I (n+1) U=F ∧ Cohort U ∧ Graded U 2 ∧ Held (carpet (Tone I)) (α/2) (Q*p) U ∧
   ∀ (G:Raw I (n+1))(t:ℝ),0≤t→ Cohort G→Graded G 1→Closing G→FirstNull G→ Held (carpet (Tone I)) σ t G→
      lineLift I n α (F-G)=U - lineLift I n α G:=by
 rcases eq_or_lt_of_le hn with rfl|he
 · exact Loop.doubleLift _ σ hσ -- subst 1? rfl orientation
 obtain ⟨α,Q,hq,hu,H,hT⟩:= line_legs I n he σ hσ
 refine ⟨α,Q,hq,hu,H,fun F p h hp hg hf _ hz=>?_⟩
 obtain ⟨ha,hc,hm,hV,hd⟩:=hT F p h hp hg hf hz
 exact ⟨ha,hc,hm,hV,fun G k hc ha hr he _ hh=>hd _ _ hc ha hr he hh⟩

/-- Fully symmetrized LITERAL curvature-coefficient existence, cost and Lipschitz difference
with uniform answer map, before block LENGTH. -/
theorem arc (σ:ℝ)(hσ:0<σ)(hn:1≤n)(V:Submodule ℝ (Urn I (n+1)))(he:adjGrade V):∃ θ K:ℝ, 0<θ∧θ≤σ∧0≤K∧
 ∀ (F:Raw I (n+1))(B:ℝ), Cloak V 1 F→0≤B→Closing F→FirstNull F→Held (carpet (Tone I)) σ B F→
   let U:=Lyapunov V (4*θ) F
   picture I (n+1) U=F∧Cloak V 2 U ∧ Held (carpet (Tone I)) θ (K*B) U∧
  ∀ (G:Raw I (n+1))(p:ℝ),Cloak V 1 G→0≤p→Closing G→FirstNull G→Held (carpet (Tone I)) σ p G→
    Lyapunov V (4*θ) (F-G)=U-Lyapunov V (4*θ) G:=by
 obtain ⟨a,Q,h,H,hQ,hR⟩:=base (I:=I) σ hσ hn
 let θ:=a/4;let u:=endFee V (a/2);have hu:0≤u:=finish_pos _ _ (by positivity) (by omega)
 refine ⟨θ,u*Q,by unfold θ;linarith,by unfold θ;linarith,by positivity,?_⟩
 intro F B hF hb hC hV hh U
 obtain ⟨hr,hP,hG,hw,hd⟩:=hR F B hb hF.path hF.field' hC hV hh
 have hz:4*θ=a:=by unfold θ;ring
 unfold U Lyapunov;rw [hz,polish_picture _ _ hG,hr, polish_keeps _ _ hF]
 refine ⟨rfl,polish_delivers _ _ hG hP he,?_,?_⟩
 · unfold θ;rw [show a/4=a/2/2 by ring,mul_assoc]
   exact bolster V _ _ _ (by positivity) (mul_nonneg hQ hb) (by omega) hP hw
 intro G p hx hp HC HS HT;rw [hd G p hp hx.path hx.field' HC HS HT,polish_sub]
end YM.RG08.Rudder.Symmetry
