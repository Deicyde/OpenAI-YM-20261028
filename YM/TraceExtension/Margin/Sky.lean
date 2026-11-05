import YM.TraceExtension.Margin.Hued
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
open Zn
variable {F:Frame G 4}{Z:Frame G 5}{n:Side}{t:ℝ}{R:Rep G n}{J:Dart G n}
open Stationary Exterior Tree Filch Lamp Loft Xo Pills
-- operational Lease = Haar local coefficient. Combined merch bloom.
variable (a:G.ColorIndex)
def MintR(F:Frame G 5)(h:G.Simple):(Axis→ F.Coeff)→L[ℝ]ℝ:= LinearMap.toContinuousLinearMap ((Lease F h).toLinearMap.comp ((Reed (Prism F)).codRestrict (Bowl F) (blade F)))
lemma MintPay (x:Axis→ Z.Coeff) (h:G.Simple)(hp:∀ i,realBar (Z.coords.symm (x i))=Z.coords.symm (x i)): (MintR Z h x:ℂ)=archK a (fun i=> Z.coords.symm (x i))/12:=by rw [← vitrine Z a x h hp]; exact Lease_paid Z a _ h
lemma MintReal(V:Axis→Peat G n)(h:∀ i, V i∈loom G n)(hp:∀ i,R.p.Regular (tempQ t) (filmR (V i)))(he:G.Simple)(hv:5 ≤R.p.order)(hx:Nonwrapping (tempQ t (n:=n)) 0)(hz:2≤ n.val):
    MintR Z he (fun i=>DCard H Z t (V i))=(Holt a (fun i=> V i ∘ input G n)).re/12:=by
    let x(i):=DCard H Z t (V i); let Q(i):= Z.coords.symm (x i); let X:= Holt a (fun i=>V i ∘input G n); have hh: X= archK a Q:= clothK a V Q (fun i=>(h i).1) (fun i U W hv=>Complex.ofReal_injective ((hp i).sites U W hv)) hx he hz fun i=>card_reads Z (hp i) hv hx
    have ht:(↑(MintR Z he x):ℂ)= (1/12:ℝ) • X:=by rw[hh,MintPay a _ he fun i=>card_realV Z (hp i) hv]; rw[Complex.real_smul]; dsimp only [Q,x]; push_cast;ring
    change MintR Z he x=X.re/12; rw [← Complex.ofReal_re (MintR Z he x),ht,Complex.smul_re]; ring
-- account tariff canonical payment ≈ Helm. No hidden θ bias.
abbrev Revise(R:Rep G n)(v: Axis→ Z.Coeff):= (R.p.threshold^ (2:ℕ))⁻¹ • v
lemma mack(V: Axis→Peat G n)(h:∀ i,V i∈loom G n)(hp:∀ i,R.p.Regular (tempQ t) (filmR (V i)))(he:G.Simple)(hv:5≤ R.p.order)(hx:Nonwrapping (tempQ t (n:=n)) 0)(hz:2≤ n.val): MintR Z he (Revise R fun i=>altoD R t H Z (V i)) =(Holt a (fun i=> V i∘input G n)).re/12:=by
   rw[← MintReal a V h hp he hv hx hz (Z:=Z) (H:=H)]; congr 1; ext1 i; change (R.p.threshold ^(2:ℕ))⁻¹ • Triple H Z t R (V i)=_; rw [pricedU Z (hp i) hv hx (h i) he le_rfl, inv_smul_smul₀ (by positivity [R.p.threshold_pos]:R.p.threshold^(2:ℕ)≠0)]
end YM.Trace.Margin
