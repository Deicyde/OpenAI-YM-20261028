import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Gel
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Parades
/-!
# Registry insertion and literal unmarked adapters

Especially `enrolling`: after integral, cluster & hole assembly
update unmarked activities (K from the same outputs, pad into
ℕ slots). Prove `Background` and `KBound` at that prescription
upon `Sound` (real), h.sym etc. premises. No assertion that the
unmarked reweighting preserves the step push without checking.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision Baler Thirst
open scoped Topology BigOperators Classical
variable {G : Gauge} {n f : Side} {S : StepData n f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S}
    {P : Teller G} {W V ι κ α β : Type} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {u : W → Site n} {v : V→Site n}

-- use for unmarked: imaginary part vanishes
def Sound (c : ℂ) := c=(↑c.re:ℂ)
lemma vouch (g : ℝ) : Sound g:= rfl
lemma Sound.mul {x y : ℂ} (a : Sound x) (b : Sound y): Sound (x*y):= by rw [show x*y=(↑(x.re*y.re):ℂ) from (Complex.ofReal_mul ..).symm ▸ congr_arg₂ HMul.hMul a b]; exact vouch _
lemma Sound.inc {x y : ℂ} (a : Sound x) (b : Sound y): Sound (x+y):= by rw [show x+y=(↑(x.re+y.re):ℂ) from (Complex.ofReal_add ..).symm ▸ congr_arg₂ HAdd.hAdd a b]; exact vouch _
lemma Sound.prod {f : ι → ℂ} (s : Finset ι) (hx : ∀ i, Sound (f i)): Sound (∏ i∈s,f i):= by
  induction s using Finset.induction_on with
  | empty=>rw [prod_empty]; exact vouch 1
  | insert i s hi h=> rw [prod_insert hi]; exact (hx i).mul h
lemma Sound.sum {f : ι → ℂ} (s : Finset ι) (hx : ∀ i, Sound (f i)): Sound (∑ i∈s,f i):= by
  induction s using Finset.induction_on with
  | empty=>rw [sum_empty]; exact vouch 0
  | insert i s hi h=> rw [sum_insert hi]; exact (hx i).inc h
lemma Sound.money {O : Orchard S} (T' : Tube G S) {U : Config G n} {p : vouchers S} {g : Shader G S x O ℂ} (he : ∀ A k V y,Sound (g A k V y)): Sound (glance T' g p U):= by
  apply Sound.sum; intro k
  let Q:=stapled x p U; let f:=g Q k U; let μ:=viewer T' Q x k.wood k.tag U
  have hv:(∫ y,f y∂μ)=(↑(∫ y,(f y).re∂μ):ℂ):= (integral_congr_ae (Filter.Eventually.of_forall (he _ _ _))).trans integral_complex_ofReal
  change Sound (k.share • ∫ y,f y∂μ); rw [hv,Complex.real_smul]; exact (vouch _).mul (vouch _)
lemma chirping {K : ι→ Lifted G u τ} {J : κ → Lining G u τ} (hk : ∀ i,(K i).fires=quiet W) (hj : ∀ i,(raised (J i)).fires=quiet W) (hi : ∀ i U,Sound ((K i).value U)) (hh : ∀ i U,Sound ((raised (J i)).value U)) i U:
    Sound ((toRain K J i).value U):= by
  rw [short_print hk hj]; split
  · exact Sound.prod _ (fun i=> by rcases i with i|i; exacts [hi i U,hh i U])
  exact vouch 0

-- pad without dependence of metadata, and use magnitude certificate **after**
-- this actual construction, to avoid circular MatricAuth. No equality of Books
-- needed a priori. All news weights real.
section
variable {d w : ℝ} [Fintype ι]
def bareBurst (K : Lifted G u τ) : Burst G n τ where
  city:= Gel.calls K
  value U:= (K.value U).re
  inv z U:= congr_arg Complex.re (K.inv z U)
  meas:= Complex.continuous_re.measurable.comp K.meas
  uses U V h he:= congr_arg Complex.re (K.only U V h he)
  flag _ h:= K.flag _ (fun he=> h (congr_arg Complex.re he))
variable {Q : Rep G n}
-- keeper republic at Rent

def seated (R : Rep G n) (K : ι→Lifted G u R.p.threshold) (i : addressKey n) := (prepare (bareBurst ∘ K) i).choose
def periodSeat (n : Side) : ℕ≃ addressKey n × ℕ := by
  haveI : Nonempty (Neat n):= ⟨⟨({0},{0}),singleton_nonempty _,subset_refl _⟩⟩
  exact (show Nonempty (ℕ≃Neat n×ℕ) from inferInstance).some

def enrolling (R : Rep G n) (K : ι→Lifted G u R.p.threshold) : Rep G n:= {R with activities:= Baler.lengthen R.activities R.p (seated R K) (periodSeat _) }
lemma chairMap (R : Rep G n) (K : ι→Lifted G u R.p.threshold) (hk : ∀ i,(K i).fires=quiet W) (hs : ∀ i U,Sound ((K i).value U)): Background (enrolling R K) K:= by
  let E:= periodSeat n; let Q:=seated R K
  intro i U
  have hi : Archive (enrolling R K).activities i U=(Q i).value U:= by
    unfold Archive
    rw [tsum_eq_single (E.symm (i,0)),if_pos,lengthenX]
    · exact congr_arg (fun j : addressKey n=>(Q j).value U) (by rw [E.apply_symm_apply])
    · rw [E.apply_symm_apply]
    · rw [show meterAddress _= _ from (show meterAddress ((enrolling R K).activities.forced (E.symm (i,0)))=(E (E.symm (i,0))).1 from rfl),E.apply_symm_apply]
    intro a hh; by_cases e : (E a).1=i
    · have ha : (E a).2≠0:= by intro h; apply hh; exact E.injective (Prod.ext (by rw [E.apply_symm_apply]; exact e) (by rw [E.apply_symm_apply]; exact h))
      split
      · exact if_neg (show ¬_ from ha)
      · rfl
    exact if_neg e
  rw [hi]; change column (τ:=R.p.threshold) K _ _ = (↑((seated R K i).value U):ℂ); dsimp only [seated]; rw [(prepare (bareBurst ∘ K) i).choose_spec.2 U, tsum_fintype, Complex.ofReal_sum]
  unfold Value.column; refine Finset.sum_congr rfl fun j _=>?_
  simp only [hk, true_and]; by_cases hh : Gel.calls (K j)=i
  · exact (if_pos (congr_arg Subtype.val hh)).trans ((hs j U).trans (congr_arg Complex.ofReal (if_pos hh).symm))
  rw [if_neg (show ((K j).extent,(K j).inventory)≠ i.val from fun h=>hh (Subtype.ext h)), if_neg (show ((bareBurst ∘ K) j).city ≠ i from hh),Complex.ofReal_zero]
where
  -- publicly composed lengthen reads
  lengthenX i U (h : ((periodSeat n) i).2=0) : ((enrolling R K).activities.K i U)= (seated R K ((periodSeat n) i).1).value U:= if_pos h
variable {r : W→ℝ}
lemma burnCost (R : Rep G n) (K : ι→Lifted G u R.p.threshold) {w} (H : Stripes R.p K r R.p.supportExponent w) (hK : ∀ i,(K i).fires=Glyph.quiet W): (enrolling R K).activities.KBound R.p w:= by
  have hp : SumHit (p:=R.p) (bareBurst ∘ K) R.p.supportExponent w:= by
    obtain ⟨b,h,H⟩:=H
    let p i:= charge R.p R.p.supportExponent (K i).extent
    let k i:= b i / p i
    have hv i :0<p i:= Real.exp_pos _; have hv' i : 0≤k i:=div_nonneg (h i).1 (hv i).le
    refine ⟨k,fun i=>⟨hv' i,fun U=>?_⟩,fun i=> ?_⟩
    · have hx: p i*1*‖(K i).value U‖ ≤ b i:= by simpa only [hK,Poly.toll,Glyph.quiet, Census.quiet,Finset.prod_empty] using (h i).2 U
      rw [mul_one,mul_comm] at hx; exact (Complex.abs_re_le_norm _).trans ((le_div_iff₀ (hv i)).2 hx)
    let f j:=if i∈(K j).extent then b j else 0
    unfold Point
    change SumBudget (Thirst.pay (fun j=> k j*p j) (fun j=>i∈(K j).extent)) w
    rw [show (fun j=>k j*p j)=b from funext fun j=>div_mul_cancel₀ _ (hv j).ne']
    refine ⟨fun j=>?_,(hasSum_fintype _).summable,?_⟩; unfold Thirst.pay; split; exact (h _).1; exact le_rfl
    rw [tsum_fintype]; refine le_trans ?_ (H i); apply Finset.sum_le_sum; intro j _; unfold Thirst.pay; split_ifs <;> exact le_rfl
  exact Baler.lengthy _ _ (fun i=> (prepare (bareBurst ∘ K) i).choose_spec.1) _ _
    (maintain (bareBurst ∘ K) hp R.p.exponent_pos.le _ (fun i=> (prepare (bareBurst ∘ K) i).choose_spec.1) (fun i=> (prepare (bareBurst ∘ K) i).choose_spec.2))
lemma transported (R : Rep G n) (K : ι→Lifted G u R.p.threshold) (hJ : ∀ s i, ∃ F, Waking (pull s i) (StepData.sendSites s i) F K K) (h : ∀ s i, Nonempty (R.activities.Moves s i)) : ∀ s i, Nonempty ((enrolling R K).activities.Moves s i):= by
  have hM : Rhythm (bareBurst ∘ K):= by
    intro s i; obtain ⟨F,H⟩:=hJ s i
    refine ⟨F,fun j=>Subtype.ext ?_,fun U j=>(congr_arg Complex.re (H.values j U)).symm⟩
    rw [sent_one]; apply Prod.ext
    exact (H.extent _).trans (Finset.map_eq_image ..); exact (H.inventory _).trans (Finset.map_eq_image ..)
  exact Baler.presented _ h _ (fun i=> (prepare (bareBurst ∘ K) i).choose_spec.1) (hymn (p:=R.p) (bareBurst ∘ K) hM _ (fun i=> (prepare (bareBurst ∘ K) i).choose_spec.1) (fun i=> (prepare (bareBurst ∘ K) i).choose_spec.2))
end
end YM.PhysicalNext.InteractingRank.Display.Sew
