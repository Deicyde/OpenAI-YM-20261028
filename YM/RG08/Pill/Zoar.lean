import YM.RG08.Pill.Marsh
/-!
# Wilson basis trajectories, expressing all matrices at declared common scale
and using previous geometric charges. Also arbitrary subsegment.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Pill
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix Summit PertExtension.Series.Tested PertExtension.Series.Radial Scores PowerSeries Door
open scoped BigOperators Topology Real ContDiff
variable {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings Summit
local notation "⨯" => (PowerSeries.X:PowerSeries ℝ)
local notation "Z" => ladder X ν D' N
section
variable {I:Type}{y δ:I→ℝ}{M A:I→Session (Letter F)}{B C:I→PowerSeries ℝ}
def awake {α:Type}(x:PowerSeries ℝ)(M: Session α) : Session α:= M.map fun f=> PowerSeries.subst x f
lemma awake_b (hp:Audience y)(h:∀ i≤e, Lying y δ (fun j=>hot (M j) i) (fun j=> hot (A j) i)) (hk: ∀ i≤e, Lease y δ (fun j=>coeff i (B j)) (fun j=>coeff i (C j))): Lying y δ (fun i=> hot (awake (⨯ * B i) (M i)) e) (fun i=> hot (awake (⨯ * C i) (A i)) e):= by
  intro i j; simp_rw [awake,hot_node,map_apply,stencilSub]; apply Lease.lists; exact hp
  intro a ha; apply Lease.times; exact h a (mem_range_succ_iff.mp ha) _ _
  · have hx:= Lease.powerT (f:=fun i k=> coeff k (B i)) (g:=fun i k=> coeff k (C i)) hp hk a _ (show e-a≤ e from Nat.sub_le ..)
    unfold powT at hx; have hh(a:PowerSeries ℝ): PowerSeries.mk (fun k=> coeff k a)=a:=by ext i; rw [coeff_mk]
    simp_rw [hh] at hx; exact hx
  exact hp
lemma awake_z {L:Side}{M:Session (Letter F)}(he: Flash L M)(p: PowerSeries ℝ) : Thick L (awake (⨯*p) M⁻¹) := by
  have ht b v: hot (awake (⨯*p) M⁻¹) 0 b v=hot M⁻¹ 0 b v:= by simp [hot_node,awake,stencilSub]
  unfold Thick; simp_rw [ht]; exact (blazing he).2
lemma awake_mul {p:PowerSeries ℝ}(h:HasSubst p)(M N : Session (Letter F)): awake p (M*N)=awake p M*awake p N:= by
  (ext i j : 1); let A: PowerSeries ℝ →ₐ[ℝ] PowerSeries ℝ:= PowerSeries.substAlgHom h
  have he: (A:(PowerSeries ℝ)→PowerSeries ℝ)=PowerSeries.subst p:=coe_substAlgHom _
  unfold awake; simp_rw [Matrix.mul_apply,map_apply] -- rewrite multiply sides
  rw [Matrix.mul_apply]; simp_rw [← he]; rw [_root_.map_sum]; exact sum_congr rfl fun k _=> _root_.map_mul ..
lemma awakenOne (p:PowerSeries ℝ)(hp:HasSubst p): awake p (1:Session (Letter F))=1:= by
   let A: PowerSeries ℝ →ₐ[ℝ] PowerSeries ℝ:= PowerSeries.substAlgHom hp; have he: (A:PowerSeries ℝ→PowerSeries ℝ)=PowerSeries.subst p:=coe_substAlgHom _
   (ext i j : 1); simp_rw [awake,map_apply, Matrix.one_apply]; rw [← he]; split_ifs <;> simp
end

-- any subsegment bounded by the two pricing endpoint clocks. Include main even if outside. geometric constants.
variable {I:Type}{u:I→Windows}
structure ShoreP (u : I→Windows) where
  next : Roam u -- upper endpoint price
  low : ℕ -- lower endpoint must ≤ next.i
  init : low ≤ next.i
  ready : (u next.b).start ≤ low
variable (σ: ShoreP u)
def ShoreP.fromR (σ:ShoreP u) : Roam u:={σ.next with i:=σ.low,geC:=σ.ready,cut:=σ.init.trans σ.next.toWings.cut}
def ShoreP.city := σ.next.i-σ.low
def ShoreP.y (X:Chain) := max (σ.fromR.measure X) (σ.next.measure X)
lemma city_one (X:Chain) : 1 ≤ σ.y X:= (sh X σ.next.toWings).trans (le_max_right ..)
lemma src_cost (X:Chain)(m:Roam u) (hp:m.b=σ.next.b) (hx:σ.low≤m.i)(hz:m.i ≤ σ.next.i): m.measure X ≤ σ.y X := by
  have hm:m.main=σ.next.main:= by unfold Roam.main; rw [hp]
  unfold Roam.measure Wings.menu Launch.farY age; change 2+ (u m.b).Z+ |X.S.scale m.i-X.S.scale m.main| ≤ _; rw [hp,hm]
  by_cases hh: m.i≤σ.next.main
  · rw [abs_of_nonpos (sub_nonpos.mpr (age_scale_mono X.S hh))]; apply le_trans (b:=σ.fromR.measure X) _ (le_max_left ..); change _ ≤ 2 + _+|X.S.scale σ.low - X.S.scale σ.next.main|; rw [abs_of_nonpos (sub_nonpos.mpr (age_scale_mono _ (hx.trans hh)))]; have hq: σ.fromR.b= σ.next.b:= rfl; rw [hq]; apply add_le_add (le_refl _) (by linarith [age_scale_mono X.S hx])
  have h := le_of_lt (lt_of_not_ge hh); rw [abs_of_nonneg (sub_nonneg.mpr (age_scale_mono _ h))]; apply le_trans (b:=σ.next.measure X) _ (le_max_right ..); change _ ≤ 2+_+ |X.S.scale σ.next.i-X.S.scale σ.next.main|; rw [abs_of_nonneg (sub_nonneg.mpr (age_scale_mono _ (h.trans hz)))]; apply add_le_add (le_refl _) (by linarith [age_scale_mono X.S hz])
omit σ in
lemma subsegment (X:Chain): Weighed (fun i:ShoreP u=> i.y X) (fun i=> (i.city:ℝ)):= by
  have hx:=geo X (u:=u); let y (i:ShoreP u):= i.y X
  have hu: Weighed y y:= by simpa only [pow_one] using Weighed.power y (fun i=>city_one i X) 1
  have ha := (hu.mono (fun i=>zero_le_one.trans (sh X (ShoreP.fromR i).toWings)) (fun (i:ShoreP u)=>le_max_left (i.fromR.measure X) (i.next.measure X))).sway (fun i=> city_one i X) (hx.transfer ShoreP.fromR)
  have he := (hu.mono (fun i=>zero_le_one.trans (sh X (ShoreP.next i).toWings)) (fun (i:ShoreP u)=>le_max_right (i.fromR.measure X) (i.next.measure X))).sway (fun i=> city_one i X) (hx.transfer ShoreP.next)
  apply (ha.plus he (fun i=>city_one i X)).mono (fun i=> Nat.cast_nonneg _); intro i; change (i.city:ℝ) ≤ (kilometer _:ℝ)+(kilometer _:ℝ); rw [← Nat.cast_add]; apply Nat.cast_le.mpr
  unfold ShoreP.city kilometer; change i.next.i-i.low ≤ spanR i.low _+ spanR i.next.i i.next.main; rw [show i.fromR.main= i.next.main from rfl]; unfold spanR; split_ifs <;> omega
end YM.RG08.Pill
