import YM.RG08.Harvest.Gild
/-!
# Testing and announcements at real centers for $g_k$ reported cluster
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Harvest
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings PowerSeries Taste Plot Plot.High
open scoped BigOperators Topology Real ContDiff Classical
variable {I J M:Type} {u:I→Windows}{n k i:ℕ}{X:Chain}{G:Gauge}{E e r d τ D j t l N:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable {b:J→ Dial u}{p:List M}{a z:M→ℕ}{φ:M→J→ Profile D}{C B:J→ℝ}{q s:M→ J→ℝ} {W l':J→ℕ}{hw:∀ i,Optic (b i) (W i)}
section points
variable (X ν D')
-- scalar covariance bank to center-test. c measure spacing, test at centered x.
def terraceP (b:J→Dial u)(W:J→ℕ)(i:J)(x:Rest):= spanP X (b i).K (W i) • x.val
def fpulse (b:J→ Dial u)(W:J→ℕ)(A:J→ M→ℕ→BoardU D R G)(p:List M)(z a:M→ℕ)(φ:M→ J→Profile D)(i:J)(x:Rest):= field_at X ν D' b A p z a φ (fun _=> terraceP X b W i x) i (W i)
def spritz (b:J→ Dial u)(W:J→ℕ)(A:J→ M→ℕ→BoardU D R G)(p:List M)(z a:M→ℕ)(φ:M→ J→Profile D)(h:1/2≤R) (i:J) := rip (fpulse X ν D' b W A p z a φ i) h D
variable {X ν D'} {V U: J→M→ℕ→BoardU D R G}
local notation "☈" => terraceP
section prelabel
lemma outings {J':Type}(f:J'→J)(hx: Fleece T b ν D' k E p z a U V q) : Fleece T (b∘f) ν D' k E p z a (U∘f) (V∘f) (fun i=>q i∘f):= by
   let H(s:High (b∘f) 0):High b 0:= ⟨f s.z,s.i,s.heap,s.scope⟩; let V(s:High (rightT (b∘f)) 0): High (rightT b) 0:=⟨f s.z,s.i,s.heap,s.scope⟩
   exact ⟨fun i=>hx.main _,fun i=>hx.side _,fun i hi t=>hx.hint i hi _,fun i hi j hj r=>(hx.prior i hi j hj r).mold H,fun i hi j hj r=>(hx.assets i hi j hj r).mold V⟩
variable [Fintype M]
local notation "♭" => fpulse X ν D'
local notation "♯" => spritz X ν D'
local notation "∀v" => Plot.tribute X b
lemma glimpse (he:Tights T S ν D' u)(hP:Fleece T b ν D' (k+(loadᵣ a p+l)) E p z a U V q)(hv:Pines A u)(hm:Mats p (Plot.tribute X b) C B s φ)(hy:loadᵣ z p ≤ τ)(hZ:∀ i∈p,z i≤τ)(hH:p.Nodup)(hd:∀ i,i∈p)(h0:1≤l)(hp: ∀ i,Optic (b i) (W i))(hE:e≤E) :
   Drum k (fun i:J×Rest=> ((civic hp i.1).y X)) (payableD X b∘Prod.fst) (accrues (q*s) p ∘ Prod.fst) (fun i=> ♭ b W U p z a φ i.1 i.2 e r) (fun i=> ♭ (rightT b) W V p z a φ i.1 i.2 e r) 1:= by
   let R': J×Rest→J:= Prod.fst
   let T' := civic (b:=b∘R') (W:=W∘R') (fun i=>hp i.1); let P i: Wall T' 0 := ⟨i, W i.1,le_rfl,(hp _).2⟩
   let U' (i:J×Rest):= ☈ X b W i.1 i.2
   let Z (i:J×Rest):= arcT X (b i.1).K (W i.1) (U' i)
   apply inbounds (X:=Z) (U:=fun i=> _) (V:=fun i=> _) (fun i=> arc_bound ..) (fun i=> city_one _ _) -- fix
   have hh:= (dictum (b:=b∘R') (C:=C∘R') (φ:=fun i=>φ i ∘ R') (W:=W ∘R') (fun i=>hp i.1) he (outings R' hP) hv (mats_hood hm R') hy hZ hH hd h0 hE U' (r:=r)).mold P
   convert hh using 1 <;> try rfl
   all_goals ext1 i; first|exact Eq.symm (rent_lo X (b∘ R') _ (fun i=>hp i.1) i)|exact Eq.symm (congr_fun (accrues_pull p (q*s) i.1 R') i)
lemma award_c (he:Tights T S ν D' u)(hP:Fleece T b ν D' (k+(loadᵣ a p+l)) E p z a U V q)(hv:Pines A u)(hm:Mats p (Plot.tribute X b) C B s φ)(hy:loadᵣ z p ≤ τ)(hZ:∀ i∈p,z i≤τ)(hH:p.Nodup)(hd:∀ i,i∈p)(h0:1≤l)(hp:∀ i,Optic (b i) (W i))(hE:e≤E)(hA:∀ i,Via G (loadᵣ z p) (♭ b W U p z a φ i))(ht:∀ i,Via G (loadᵣ z p) (♭ (rightT b) W V p z a φ i)) :
    Drum k (fun i=> (civic hp i).y X) (payableD X b) (accrues (q*s) p) (fun i=>♯ b W U p z a φ h i e r) (fun i=>♯ (rightT b) W V p z a φ h i e r) 1:= by
   have hr:= glimpse he hP hv hm hy hZ hH hd h0 hp hE (r:=r); exact pane_d h hA ht (fun i=>city_one _ _) (pow_pr (fun i hi x=> mul_nonneg (hP.hint i hi _) (hm.zero i hi _))) (fun _=>(gain_pos ..).le) hr
end prelabel
lemma spritz_has {i':J} (hp:Via G k (fpulse X ν D' b W U p z a φ i'))(h:1/2≤R): Marvel k (spritz X ν D' b W U p z a φ h i')∧Lank (spritz X ν D' b W U p z a φ h i'):= burdens h hp
end points
end YM.RG08.Harvest
