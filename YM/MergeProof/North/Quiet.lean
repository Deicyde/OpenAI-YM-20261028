import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Leibniz
import YM.MergeProof.Magma
import YM.MergeProof.North.Islands
import YM.MergeProof.North.Mulberry
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment




set_option autoImplicit false
noncomputable section
namespace YM.Merge.Photo
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Supply
open PhysicalNext.Repeat Mallow Lotus Ovens Motion Switch Merge.Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι:Type}[Fintype ι]{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open YM.MergeProof YM.MergeProof.Ribbons YM.MergeProof.Ribbon Menu Marker Extra.Histories Accent
variable {V :Type}[Fintype V][DecidableEq V]{b:Site c}{m₀:Extra.Histories.Motion} (M:ι→Hat (Aged V) R)(Y:Cash W x μ L Q o C T R) (χ: Chi) (A:Rep G c) (rA: Ribbon.Name V→ℝ) (K:ℝ → Finset ι → Code G c)
set_option quotPrecheck false
local notation "F₀"=> fun i=> Menu.sumFee (M i) rA
local notation "I₀"=> fun i=> (M i).M
local notation "G₀"=> fun i=> Menu.sing (M i) rA
local notation "Y₀"=> spine (I₀) Y χ (F₀) (Aged V) (G₀)
local notation "K₀"=> chain A K (Aged V) (G₀)
variable {u v:V}{d e p:ℝ}{D: Equiv.Perm V}{B: Equiv.Perm ι}
    {π: R.activities.Moves m₀.1 (S.ratio.embed b)} (he: Kin M v u D m₀ (S.ratio.embed b) π B)
    (hA : Usable (fun i=> (M i).M) Y χ A (fun i=>sumFee (M i) rA) K d e p)(hw:∀ i,0 < rA i) (hx:∀ i:Bool,rA (v,i)=rA (u,i))
local notation "a"=> Match.swing Y π
local notation "c₀"=> headSheet (I₀) Y χ (F₀) (Aged V) (G₀)
local notation "K'"=> Fleece K (Aged V) (G₀)
local notation "TX"=> sky m₀ b
-- helper arbitrary tallies
include he hw hA hx
variable (U:Config G c)
omit hw in
lemma silver (i:Y.fragrances) : Harm v D m₀ ((c₀) i (pull m₀.1 b U)) (c₀ ((a).furrow i) U):=by
    obtain ⟨f,h,hp⟩:= hA.exponent -- extra
    obtain ⟨g,hg⟩:= (h i).works (pull m₀.1 b U); obtain ⟨j,hj⟩:= (h ((a).furrow i)).works U
    apply he.riot hx _ _ _ _ hg hj
    intro t s hs; apply congr_arg₂ (·-·)
    · exact (Merge.gold1 (I₀) π Y χ U t B (F₀) s (fun i hi=> ⟨(he.plot i (hs i hi)).2.1, he.fares hx i (hs i hi)⟩) i).symm -- exact change note image
    have hp:= Merge.gold1 (I₀) π Y χ U 0 B (F₀) ∅ (fun i (hh:i∈(∅:Finset ι))=>by simp at hh) i; rw [Finset.image_empty] at hp; exact hp.symm
lemma cloud (s: Support c): Harm v D m₀ (Y₀ s (pull m₀.1 b U)) (Y₀ ((TX) s) U):=by
    let e i:= Y.bookFoot (Sum.inr i); let P:Equiv.Perm Y.fragrances:= (a).furrow
    let f W i:= (c₀) i W
    have hv W s:Summable (fun i:{x// e x=s}=> f W i.val):= ((Towed.repair (flag_E (I₀) Y χ A (F₀) K (Aged V) (G₀) hA rA hw (fun i=> Menu.paid _ hw)) hw W).2).comp_injective Subtype.val_injective
    have he' i:e (P i)=TX (e i):= by rw [shading]; exact (a).alcove (.inr i)
    intro p hp; unfold spine Accent.tally; rw [Poly.share (hv U (TX s)),Poly.share (hv _ s)];
    let b': {i// e i=s}≃{i// e i=TX s}:= Equiv.subtypeEquiv P (show ∀ i,e i=s ↔ e (P i)=TX s from fun i=> by rw [he',Equiv.apply_eq_iff_eq]); rw [← b'.tsum_eq,Extra.Histories.Motion.scalar_tsum]; exact tsum_congr fun i=>silver M Y χ A rA K he hA hx U i.val p hp
lemma night (m:A.activities.Moves m₀.1 b)(h:∀ (t:ℝ)(z:Finset ι),(∀ i∈z,Focused v (M i).s)→ ∀ i, K t (z.image B) (m.kp i) U=K t z i (pull m₀.1 b U)) (q:Box c): Harm v D m₀ ((K₀) q (pull m₀.1 b U)) ((K₀) (puff m₀ b q) U):=by
    let e:=barcode A.activities; let TX':= puff m₀ b; let P:=m.kp; have he' i:e (P i)= TX' (e i):= location ..
    have hv U q:Summable (fun i:{x// e x=q}=> K' i.val U):= ((Towed.repair (flag_K A K (Aged V) (G₀) rA hw (fun i=> Menu.paid _ hw) hA.gas A.p.exponent_pos.le) hw U).2).comp_injective Subtype.val_injective
    obtain ⟨y,hY,h'⟩:=hA.gas.bought
    intro p hp; unfold chain Accent.tally; rw [Poly.share (hv U (TX' q)),Poly.share (hv _ q)];
    let b': {i// e i=q}≃{i// e i=TX' q}:= Equiv.subtypeEquiv P (show ∀ i,e i=q ↔ e (P i)=TX' q from fun i=> by rw [he',Equiv.apply_eq_iff_eq]); rw [← b'.tsum_eq,Extra.Histories.Motion.scalar_tsum]
    refine tsum_congr fun i=> he.riot hx _ _ _ _ ((hY i.val).works _).choose_spec ((hY (P i.val)).works _).choose_spec (fun t u hv=> h t u hv i.val) p hp
end YM.Merge.Photo
