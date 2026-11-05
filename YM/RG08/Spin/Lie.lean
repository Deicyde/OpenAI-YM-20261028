import YM.RG08.Spin.Felts
/-! # Orientation action on our real address+stencil labels. Multiplication convention compatible to Frame. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Spin
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{H:Hol G} {c : Side}
variable (s:Signed)
def degreeT (F:Labels.Frame G d)(i: F.Index): Finset F.Index := univ.filter (fun j=>F.grades i=F.grades j)
lemma degF (i j:F.Index) : j∈degreeT F i ↔ F.grades i=F.grades j := by simp [degreeT]
def actor (F:Labels.Frame G d)(s:Signed) (i b:F.Index):= (F.act s.ortho (Place.copy F b) i).re
lemma pin_copy (i:F.Index) : Place.copy F i=F.coords (F.basis i) := (F.coords_basis i).symm
lemma thresh (i b:F.Index)(he : F.grades b ≠ F.grades i) : actor F s i b=0:= by
   unfold actor; rw [pin_copy,F.act_coords,F.power_coefficient _ he]; rfl
   have hx:= gradePart_mem (F.grades b) (Labels.tensor s.ortho (F.basis b)); rwa [gradePart_turn,gradePart_self _ _ (F.pure b)] at hx
lemma pina (i b:F.Index): F.act s.ortho (Place.copy F b) i=(actor F s i b:ℂ):= by
   unfold actor; rw [pin_copy,F.act_coords]; let v:= Labels.tensor s.ortho (F.basis b); have ht: Labels.realBar v=v:= by unfold v; rw [Labels.real_turn,F.realForm]
   have hx:= F.conj_basis (F.coords v) i; rw [LinearEquiv.symm_apply_apply,ht] at hx; exact (Complex.conj_eq_iff_re.mp hx.symm).symm
lemma spreadsF (i:F.Index) : F.act s.ortho (Place.copy F i) = ∑ j∈degreeT F i, (actor F s j i:ℂ) • Place.copy F j := by
    funext j; rw [pina, Finset.sum_apply]; by_cases he:F.grades i=F.grades j
    · rw [sum_eq_single_of_mem j ((degF i j).mpr he)]; · simp [Place.copy]
      intro a _ ha; simp [Place.copy, Pi.single_eq_of_ne (Ne.symm ha)]
    rw [thresh s j i he,Complex.ofReal_zero, sum_eq_zero]; intro a ha; rw [degF] at ha; have hn : j≠a:=by rintro rfl; exact he ha
    simp [Place.copy,Pi.single_eq_of_ne hn]
-- nested transmission orientation retaining derivative budget by same cashT. Avoid use of perm proofs in support horizon.
def sameO (u v:Letter F) := F.grades u.label=F.grades v.label ∧ cashT u.test=cashT v.test
instance (b a:Letter F): Decidable (sameO b a):= by unfold sameO; infer_instance
lemma sameF {b a:Letter F}(h:sameO b a) : fee b=fee a ∧ slot b=slot a := by unfold fee slot; rw [h.1,h.2]; simp
-- real spin produced by data. Not necessarily orthonormal in this basis.
def bankO (s:Signed)(F:Labels.Frame G d)(D:ℕ): Loft F:= Matrix.of fun i j=>if sameO i j then actor F s i.label j.label * appoint j.test (twisting s (coinsT D i.test)) else 0
def fluxO (s: Signed)(F:Labels.Frame G d)(D:ℕ) : Session (Letter F):= Matrix.of fun i j => PowerSeries.C (bankO s F D i j)
lemma isFlux (i j:Letter F): coeff e (fluxO s F D i j)=if e=0 then bankO s F D i j else 0:= by rw [fluxO,Matrix.of_apply, PowerSeries.coeff_C]
lemma scope_b (b:Letter F) (u) : u∈ (univ:Finset (Letter F)).filter (sameO b) ↔ sameO b u:= by simp
lemma sym_so (b i:Letter F): sameO b i ↔ sameO i b:= by simp [sameO,eq_comm]
def pairSet (b: Letter F): Finset (F.Index×Cham) := degreeT F b.label ×ˢ bandP (cashT b.test)
lemma lift_here (b:Letter F)(t)(ht:t∈pairSet b): ∃ l:Letter F,sameO b l∧t=(l.label,l.test):= by
    obtain ⟨i,j⟩:=t; obtain ⟨he,hz⟩:= mem_product.mp ht; have hg:= (degF _ _).mp he; have hx:= (band_coin ..).mp hz
    dsimp only at hg hx
    exact ⟨⟨i,j,by rw [← hg,hx]; exact b.bill⟩,⟨hg,hx.symm⟩,rfl⟩
lemma spin_sum {E:Type}[AddCommMonoid E](b:Letter F)(f: F.Index→Cham→E)(Z: Letter F→E)(h : ∀ i,sameO b i → f i.label i.test=Z i) : (∑ i∈degreeT F b.label, ∑ j∈bandP (cashT b.test), f i j)=∑ i∈ (univ:Finset (Letter F)).filter (sameO b), Z i := by
    classical
    rw [← sum_product']; symm; refine Finset.sum_bij (fun j _=> (j.label,j.test)) (fun j hj=>?_) ?_ ?_ ?_
    · have he:= (scope_b b j).mp hj; exact mem_product.mpr ⟨(degF _ _).2 he.1,(band_coin ..).2 he.2.symm⟩
    · rintro ⟨a,b,h⟩ _ ⟨a',b',h'⟩ _ he; have hx:a=a':= congr_arg Prod.fst he; have hg:b=b':= congr_arg Prod.snd he; simp [hx,hg]
    · intro v hv; obtain ⟨i,hi,rfl⟩:= lift_here b v hv; exact ⟨i,(scope_b b i).2 hi,rfl⟩
    intro i hi; exact (h i ((scope_b b i).1 hi)).symm
lemma dilation_O : Dilation (fluxO s F D):= by
    constructor; intro i b v h; rw [hot_node,isFlux] at h; split at h; next he=>
      rw [bankO,Matrix.of_apply] at h; split at h; next hx=> rw [(sameF hx).2]; omega
      exact (h rfl).elim
    exact (h rfl).elim
end YM.RG08.Spin
