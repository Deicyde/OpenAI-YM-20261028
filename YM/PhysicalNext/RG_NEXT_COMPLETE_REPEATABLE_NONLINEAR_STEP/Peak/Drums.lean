import YM.AnalyticBridge.SECTOR_AFFINE_JETS.OffsetStage
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Geyser
import YM.Planned.ATOM_GUARDED_LAYOUT.Fine
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Peak
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure Planned.AtomRegular MultiNext.SignedSource WardBin.Lies Foliage
open JointLoad JointLoad.Heir
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {g : outfit G f c} {X : Support f} {Y : Support c} {Q M C' t r x z δ N ε τ : ℝ} {I : Type}
    {A : Stores S} {n i j l : ℕ} {D' : Slab G c l} {u : ℝ} {q : Chi} {d : ℝ} {f' : Config G f → ℝ}
    {o : Site f}{C : Libretto G n}{D : Record}
variable [Fintype I] (h : Plays C D P B Pt T x) (a: Museum F x A X Y I) (hf:B.Regular X f') (hp:o∈X)(hτ:B.supBounds o X f' τ)
variable (hu:0≤u)(hV: Healthy P.threshold Y V) (U:Config G f) (w:Prices G I)
    (hw:u*‖tape w‖≤D.ε*B.threshold)
-- general PC points. smooth auth irrespective of H.Pi zeros.
include h hf hp hV hu hw
local notation "Z" => a.received k T q d u
omit hp in
lemma clue : ContDiffAt ℝ n (fun y:Directions G c×Prices G I=> f' (a.received k T q d u (increment V y.1) U y.2)) (0,w):=by
  obtain ⟨g,hg⟩:= framed a hV h.space (by have ht:= h.rehearsed.test; have hh:=P.order_ge; omega) h.rehearsed.wire
  have hW := h.rehearsed; have hr:= hW.tensions
  have ht: Healthy B.threshold X (Z V U w):= border_healthy h.sew C.width C.price hW.early (h.acts F k) D.majorant (by have ht:=hW.test; have he:=P.order_ge; omega) hr a h.bulletin C.Z rfl hW.wire h.space hW.temp_eq hV U w hu hw B.threshold_pos -- border needs hG? inspect
  exact a.joint_receives (h.acts F k) h.bulletin hg U C.C_one hr.allows (fun g=> (a.extra_size g u hu w).trans (hw.trans hr.noise)) hf hW.orders ht

include hτ
local notation "Z1" => grandFee C.rights * (ample n X P B D.Q C.M C.C x)^n * τ
lemma wind (hl:l≤n)(hd:∀ j,P.dirBound (S.ratio.parent o) (D' j)):
    let g'₀ (V:Config G c):=f' (a.received k T q d u V U w)
    ContDiffAt ℝ n (g'₀ ∘ journey V l D') 0 ∧ ∀ j ≤ n, ‖iteratedFDeriv ℝ j (g'₀ ∘ journey V l D') 0‖ ≤ Z1:=by
  intro f₀; let r:= D.r; have hc:=h.rehearsed; have ht:=hc.tensions; have hC:= C.C_one; have hM:= C.matins; have hw₁:= hw.trans ht.noise
  have hn: 2≤ n:=by have hb:=hc.test; have h:=P.order_ge; omega
  have hW: Healthy B.threshold X (Z V U w):= border_healthy h.sew C.width C.price hc.early (h.acts F k) D.majorant (by omega) ht a h.bulletin C.Z rfl hc.wire h.space hc.temp_eq hV U w hu hw B.threshold_pos
  obtain ⟨g,hp'⟩:=framed a hV h.space (by omega) hc.wire
  have hw₂ g : _:= (a.extra_size g u hu w).trans hw₁
  let z:= a.overture T k V g w u D'; let f:= f' ∘ increment (Z V U w)
  have hs := (le_mul_of_one_le_left ((mul_nonneg hu (norm_nonneg _)).trans hw₁) D.majorant).trans (ht.small.trans (min_le_right ..))
  obtain ⟨hz,hz'⟩:= a.reprise (h.acts F k) hp' (h.stages F) hp D.majorant hC hM hn hl hc.temp_eq ht.coarse hc.powers hs ht.allows.le hw₂ hd
  have h0 : z 0=0:=by unfold z Museum.overture; rw [Sample.journey_origin,a.overt_home]
  have hf' : ContDiffAt ℝ n f (z 0):= h0.symm ▸ (hf.smooth _ hW).of_le (Nat.cast_le.mpr hc.orders)
  have HH := a.overt_at (q:=q) (d:=d) (h.acts F k) h.bulletin hp' U hC ht.allows hw₂ (W:=fun _=>w) (flowJourney V D') ?ready -- W notation!
  case ready =>
    intro i hi
    let L y:=a.pane V u w (g i) i (journey V l D' y) w
    have hL : ContDiffAt ℝ n L 0:= (((hp'.fits i hi).ready D').prodMk contDiffAt_const).prodMk contDiffAt_const
    have hβ : L 0=a.pane V u w (g i) i V w := by unfold L; rw [Sample.journey_origin];
    exact hβ ▸ hL.continuousAt.tendsto
  have heq : f₀ ∘ journey V l D'=ᶠ[𝓝 0] f ∘ z := HH.mono fun _ hv=> hf.sites _ _ hv
  refine ⟨(hf'.comp _ hz).congr_of_eventuallyEq heq,fun j hj=>?_⟩
  rw [(heq.iteratedFDeriv (𝕜:=ℝ) _).eq_of_nhds]; let A:= ample n X P B D.Q C.M C.C x; have hA:1≤A:= ample_one n X P B D.majorant hM hC
  have ht:= hτ.1; have hQ:= C.rights.large
  rw [grandFee,show ample n X P B D.Q C.M C.C x=A from rfl,show (patterns n*C.rights.fee)*A^n*τ=patterns n*(A^n*C.rights.fee*τ) by ring]; refine slots_bound hz hf' hj (by positivity : 0≤ A^n*C.rights.fee*τ) (fun p v hv=>?_); rw [h0]
  refine (C.rights.born _ _ (fun _=>A) (p.length_le.trans hj) ((p.length_le.trans hj).trans hc.orders) hf hτ hW
    (fun i=> hz' _ (p.partSize_pos i) ((p.partSize_le i).trans hj) _ (fun _=> hv _))).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; gcongr; exact p.length_le.trans hj

def lumen (m:ℕ)(M:ℝ)(U: Rights G n)(L:Side)(X:Support f)(P B:BudgetPoint)(C:Libretto G n)(D:Record)(x u:ℝ)(z:Prices G I) := tinyR m U*(M+trancheD m L n D.Q (loom P (reach x) C.C) (u*‖tape z‖) B.threshold)^n*((L.val:ℝ)⁻¹)^(m+1) + 0*(X.card:ℝ)
lemma creek (Q: Rights G n)(ht: Short S B X)(hr: lit o X f' i)(hS: i+1 ≤ n)(hl:l≤n)(hd:∀ j,P.dirBound (S.ratio.parent o) (D' j))(hg: glider G T i B.power (2*C.C) M)(hy:1≤M):
    let g'₀ (V:Config G c):=f' (a.received k T q d u V U w)
    ContDiffAt ℝ n (g'₀ ∘ journey V l D') 0 ∧ ∀ j≤ n, ‖iteratedFDeriv ℝ j (g'₀ ∘ journey V l D') 0‖ ≤ lumen i M Q S.patch.L X P B C D x u w * τ:=by
   intro f₀; have hc:=h.rehearsed; have hK : 2≤n:=by have hp:=hc.test; have he:= P.order_ge; omega
   have hZ:= hc.tensions
   have hX: Healthy B.threshold X (Z V U w):= border_healthy h.sew C.width C.price hc.early (h.acts F k) D.majorant hK hZ a h.bulletin C.Z rfl hc.wire h.space hc.temp_eq hV U w hu hw B.threshold_pos
   obtain ⟨g,hβ⟩:= a.canvas o (Finset.mem_union_left _ hp) hV h.space C.Z (by omega) hc.wire
   unfold lumen; simp_rw [zero_mul,add_zero]; exact airbud Q a h.bulletin hc.weft (h.acts F k) hβ C.C_one hg D.majorant hy hK hS hc.orders h.space hc.temp_eq hZ.coarse hc.powers hZ.allows (hZ.small.trans (min_le_right ..)) ht hf hp hr hτ hd hl U w hX hu (hw.trans hZ.noise)
end YM.PhysicalNext.Repeat.Peak
