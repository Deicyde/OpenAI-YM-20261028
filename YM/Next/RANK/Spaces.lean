import YM.Next.RANK.Bordering
import YM.Next.RANK.TrueWind
import YM.Org.Input

/-!
# Move the Regular masks at restart

First keep OLD exponent formula, canonical X scale.
On short bits of marker move to common Q. Supports with false case cannot be
forgotten even on $τ$ fields that pass all other tests. Long bits use Legend.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells  Finset Baler Source Labels
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {N k i R d p : ℕ} (v : C.label d) (H : C.Makes) (hk : C.ref d≤ k) (hN : k≤N)
variable (i k N p : ℕ)

-- unmasked big classification. Ord the only global-one.
def ord (x : nearIndex C v i k N p) := x= .inl (.inl ())

def ten (j : nearIndex C v i k N p) (U : Config G (C.side k p)) := nearW C v i k N p j * if ord v i k N p j then
    nearA C v i k N p j U else masked (C.path.rep N p k).p.threshold (nearX C v i k N p j) (nearA C v i k N p j) U

def glance (U : Config G (C.side k p)):=∑' i':nearIndex C v i k N p, ten v i k N p i' U

def glare (U : Config G (C.side k p)):=∑' i':wideIndex C v i k N p, wideW C v i k N p i' *
      masked (C.path.rep N p k).p.threshold (wideX C v i k N p i') (wideA C v i k N p i') U
variable {i k N p}

-- standard relation without erasing masks
lemma cost_ex (v : C.label d) (H : C.Makes) (hk : C.ref d ≤ k) (hN : k ≤ N) i (U : Config G (C.side k p)) :
    awakeFull C k N p v U=glance v i k N p U+glare v i k N p U:= by
  let A:= C.path.rep N p k; let s:=A.p; let K:= parcel C d k N p v
  let V:= C.labels.level d; let O:= C.localSection d
  let b:=setOf (smalls C i k N p v); let o:Site (C.side k p):=0
  let z:=pinHat C d k
  have hF:= H.calibrated d N p (hk.trans hN)
  have he:=hF.cap k hk hN ((C.factory d N p).terminal.symm v)
  let f x:=K.maskedTerm A x U
  let g x:=z*f x
  have hf : Summable g:= ((Coefficient.regular_series he).summable U).mul_left z
  let T x:=ten v i k N p x U
  have hx (x:b) : T (Sum.inr x) = g x.val:= by
    dsimp only [T,ten];split
    · rename_i h; cases h
    change z*1*_= _; rw [mul_one]; rfl
  have ht : Summable (T∘ Sum.inr):= (hf.subtype b).congr (fun i=> (hx i).symm)
  change z*_=(∑' i,T i)+(∑' x:↥(bᶜ),g x.val); rw [Summable.tsum_sum (f:=T) (hasSum_fintype _).summable ht]; simp_rw [hx]; rw [tsum_fintype,add_assoc]
  change z*(K.exponentialEntry 0 O A U)= (∑ i,T (Sum.inl i)) + ((∑' x:b,g x.val)+_)
  rw [Summable.tsum_add_tsum_compl (f:=g) (s:=b) (hf.subtype b) (hf.subtype _), tsum_mul_left]
  rw [Coefficient.exponentialEntry,mul_add]; congr 1
  -- moon. pull actual masks at all orientations!
  let v':= V.scaled s.threshold⁻¹ (V.core K.x)
  let M:= Healthy s.threshold (O.footprint o) U; unfold LA; rw [Fintype.sum_sum_type,Fintype.sum_unique];
  have he':T (.inl (.inl ()))= z*K.x 0 := by
    dsimp only [T,ten]; rw [if_pos (show ord v i k N p _ from rfl)]; change z*_*(1:ℂ)=_;rw [mul_one];rfl
  rw [he']; change z*(_+masked s.threshold _ (O.places v' o) U)=z* _+ _
  rw [mul_add]; congr 1
  by_cases h:M
  · rw [masked_eq _ _ _ _ h]
    have hq : ∑ j : V.Index, T (.inl (.inr j)) = z*(∑ j: V.Index,v' j*O.places (Pi.single j 1) o U):= by
      rw [mul_sum]; apply sum_congr rfl; intro j _; dsimp only [T,ten]; split_ifs with he
      · cases he
      change z*(_ : ℂ)*masked s.threshold (O.footprint o) _ U= _; rw [masked_eq _ _ _ _ (show _ from h)];exact mul_assoc ..
    rw [hq]; apply congr_arg; have hp' : v'=∑ i,v' i • Pi.single i 1 := by ext i; simp [Pi.single_apply]
    conv_lhs=>rw [hp'];
    unfold SectionData.places SectionData.evaluate; rw [map_sum,map_sum]; simp_rw [map_smul];rfl
  rw [masked_ne _ _ _ _ h,mul_zero]; symm; apply Finset.sum_eq_zero; intro i _; dsimp only [T,ten]; split_ifs with he
  · cases he
  change (_:ℂ)*masked s.threshold (O.footprint o) _ U=_; rw [masked_ne _ _ _ _ h,mul_zero]

-- short unmasked function on cube. receipt |

lemma income_ten (v : C.label d) (H : C.Makes) (hk : C.ref d ≤ k) (hN : k≤N) i (U : Config G (C.side k p)) : ‖glance v i k N p U‖≤3*moneys C d k N p v:= by
  obtain ⟨e,he,hv⟩:= (Spindle.receipts C i H hk hN v p).1.pays
  let s:= (C.path.rep N p k).p
  have h₁ j: ‖ten v i k N p j U‖≤ ‖nearW C v i k N p j‖*e j:= by
    obtain ⟨hz,hp⟩:=he j; unfold ten; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    by_cases hh:ord v i k N p j
    · change j= .inl (.inl ()) at hh; subst j; rw [if_pos (show ord v i k N p _ from rfl)]
      change ‖(1:ℂ)‖≤_
      have ht:Healthy s.threshold (nearX C v i k N p (.inl (.inl ()))) (1:Config G (C.side k p)):= by
        apply Finset.disjoint_left.mpr; intro j hj hk; obtain ⟨q,hq,h⟩:= (flags_spec ..).1 hk
        have hs : ∀ (x : Site (C.side k p)) (l : Walk), travel (K:=G.El) 1 x l =1:=by
          intro x l; induction l generalizing x with | nil=> simp [travel] | cons a l IH=> rw [travel,IH]; unfold Step.read;split<;>simp
        rw [faceValue,hs,Gauge.chord_one] at h; linarith only [s.threshold_pos,h]
      exact hp.2 1 ht [] (Nat.zero_le _) (by simp)
    rw [if_neg hh]; by_cases hh:Healthy s.threshold (nearX C v i k N p j) U
    · rw [masked_eq _ _ _ _ hh]; exact hp.2 U hh [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hh,norm_zero]; exact hp.1
  have hf:= hv.2.1.of_nonneg_of_le (fun i=> norm_nonneg _) h₁; exact (norm_tsum_le_tsum_norm hf).trans ((hf.tsum_le_tsum h₁ hv.2.1).trans hv.2.2)

structure HealthyCube (C : Family G) (v : C.label d) (i k N p : ℕ) (Q : Support (C.side k p)) : Prop where
  extents j : nearX C v i k N p j ⊆ Q

structure Reliable (b : ℝ) (G : Gauge) (n : Side) (Q : Support n) (F : Config G n→ℂ) : Prop where
  inv : GaugeInvariant F
  meas : Measurable F
  locally : LocalOn Q F

lemma reads_glance (v : C.label d) (H : C.Makes) (hk : C.ref d≤k) (hN : k≤N) (p i) {Q} (hp : HealthyCube C v i k N p Q) :
    let b:= (C.path.rep N p k).p.threshold
    Reliable b G _ (halo 8 Q) (glance v i k N p) ∧ Reliable b G _ Q (nearHol C v i k N p) ∧ ∀ U, Healthy b Q U→ glance v i k N p U= nearHol C v i k N p U:= by
  intro b; obtain ⟨e,he,hv⟩:= (Spindle.receipts C i H hk hN v p).1.pays
  let a j:= nearX C v i k N p j;let W j:= nearA C v i k N p j;let T j:= ten v i k N p j
  have ht (j) : Reliable b G _ (halo 8 (a j)) (T j):= by
    have hx:= he j |>.1
    constructor
    · intro k' U; unfold T ten; split; exact congr_arg _ (hx.symmetry k' U); exact congr_arg _ (sails _ _ _ hx.symmetry k' U)
    · apply measurable_const.mul; split;exact hx.borel;exact masked_measurable _ _ _ hx.borel
    intro U V h; unfold T ten; apply congr_arg; split
    · exact hx.sites _ _ (agrees_mono h (fun i hi=> halo_subset _ _ hi))
    exact sail _ _ _ hx.sites U V h
  refine ⟨⟨fun k U=>tsum_congr fun j=> (ht j).inv ..,?_,fun U V h=> tsum_congr fun j=> (ht j).locally U V (agrees_mono h fun i hi=> halo_mono le_rfl (hp.extents j) hi)⟩,⟨?_,?_,?_⟩,fun U hh=>?_⟩
  · exact Measurable.tsum (fun i=> (ht i).meas)
  · intro k' U; apply tsum_congr; intro i; rw [(he i|>.1.symmetry) k' U]
  · apply Measurable.tsum; intro i; exact measurable_const.mul (he i|>.1.borel)
  · intro U V hh; apply tsum_congr; intro j; exact congr_arg _ ((he j).1.sites U V (agrees_mono hh fun i ht=> hp.extents j ht))
  apply tsum_congr; intro j; unfold ten; split
  · rfl
  rw [masked_eq _ _ _ _ (Disjoint.mono_left (hp.extents j) hh)]
end YM.Next.Rank.Edition
