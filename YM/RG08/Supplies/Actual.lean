import YM.RG08.Supplies.Assemble
import YM.RG08.Reports.Receipt

/-!
# Extra post-L receipts to retain the ultraviolet cover Gamma and A_tr FOR PERTURBATIVE consumers
on the very same construction.
-/
noncomputable section
namespace YM.RG08.Supplies
open Function Filter Lattice RG Tree Wilson Laurent Precision Pert.Bulk RG08.Flat RG08.Packets RG08.Line Stationary Bloch Matrix RG08.Rows RG08.Cell
open Function Set Filter MeasureTheory PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Extraction Org Table Spec MergeProof
open UVExtension RG08
open scoped Classical Matrix Topology BigOperators ENNReal
set_option autoImplicit false
variable {G : Gauge} {a:Levels G} {H:Horizon a} {X P:MapPrices}

-- width prices also post (the width itself fixed pre-block, but reciprocal for a/mu kernels can
-- be billed to beta before later estimates). Announce all extras required jointly. For example,
-- at two-position joins v just enough for y_i bound; for real rendering need slower z_m delays. Here
-- choose retarded delay log(log beta) for everything. z_i can include finite exponent constants
-- depending on G etc; expose receipts directly for integrators.

def rankDelay (a:Levels G)(P X:MapPrices) (i j:ℕ) :=
   max (P.Ω j) (max (X.Ω j) (max (Strip G P X a.clock.kernel j)⁻¹ (max ((a.S.block i).val:ℝ) (delay G P a.clock.kernel j (a.S.block i)))))

def slow (P X : MapPrices)(K:KernelChoices)(L:ℕ→ℕ)(j:ℕ) :=
  Real.exp (Real.exp ((max (max (P.Ω (j-1)) (X.Ω (j-1))) (max (P.Ω j) (max (X.Ω j) (max (Strip G P X K j)⁻¹ (max (L j:ℝ) (delay G P K j ⟨max (L j) 1,by omega⟩))))))))

lemma heatSame (hG:G.Simple)(b:ℝ)(hb:0<b):
    ∃ (C : Family G) (f : Extraction.Order) (T : YM.Table C.book)
      (F : Spec.Final C f T) (A : EveryPhase.Almanac F), C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty = b ∧ Oasis.Floral (hG:=hG) C ∧
      (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
      (∀ d k : ℕ, ∀ᶠ n in atTop,
        ∀ (r : ℕ) (v : Fin r → C.book.Token), (∀ i,(v i).1≤d) → ∃ g, Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed F A ∧
        ∃ (s:Supply.Sheet G)(P₀ X:MapPrices)(H:Horizon C.path.levels)(G₀:ℕ→Pert.Bulk.Kernel Flat.Links Flat.Links)(A B:ℝ)(d l:ℕ)(c:ℝ),
          let a:= C.path.levels; let P:=UVExtension.Case.actualPay s P₀
          a.clock.kernel=s.kernel ∧ a.clock.stage=s.profile ∧ H.Suffices P ∧
          (∀ (N i p:ℕ),i≤N → Attached (H.H N i) (C.path.rep N p i).path) ∧
          (∀ i,rankDelay a P X i (a.clock.J (i+1)) ≤ Real.log (Real.log (a.clock.hatBeta i))) ∧
          Quorum (curve X) G₀ 0 H A B d l c ∧ ∃ C r, Pallet G a.clock.kernel a H (Strip G P X a.clock.kernel) C r c:= by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b hb
  have h (s:Supply.Sheet G) := entrance_gate hG s.kernel s rfl
  choose X E Hx using h
  let D (s:Supply.Sheet G) (P:MapPrices) := slow (G:=G) (UVExtension.Case.actualPay s P) (X s) s.kernel
  obtain ⟨C,f,T,F,A,hF,hT,hκ,hO,hA,hD,hP,s,p,H,hg⟩:= Reports.paid hG k hp (fun s _=> E s) D
  let a:= C.path.levels
  let P:=UVExtension.Case.actualPay s p
  have hN (m:ℕ) : E s (a.clock.J (m+1)) ≤ (a.S.block m).val := by rw [← a.fits.sameFactor]; exact hg.cluster _
  have ht i: let j:=a.clock.J (i+1); max (max (P.Ω (j-1)) ((X s).Ω (j-1))) (rankDelay a P (X s) i j) ≤ Real.log (Real.log (a.clock.hatBeta i)):=by
    intro j
    have he := hg.payment i
    let v:= fun i=>(a.clock.factor i).val
    change slow P (X s) s.kernel v j ≤ _ at he
    have hx : s.kernel=a.clock.kernel:=hg.kernel.symm
    unfold slow at he
    have hlength : v j=(a.S.block i).val := congr_arg Subtype.val (a.fits.sameFactor i)
    rw [hx, show (⟨max (v j) 1,_⟩:Side)=a.S.block i by ext; dsimp; rw [hlength,max_eq_left (a.S.block i).pos]; rfl, hlength] at he
    apply le_trans _ (Real.log_le_log ?_ (Real.log_le_log (Real.exp_pos _) he))
    · simp only [Real.log_exp]; exact le_refl _
    simp only [Real.log_exp]; exact Real.exp_pos _
  have hv: Available G a P:=by
    intro i
    have he:= ht i; unfold rankDelay at he; unfold Lambda
    have hy := Real.add_one_le_exp (Real.log (Real.log (a.clock.hatBeta i)))
    rw [Real.exp_log (Real.log_pos (a.fits.delayed i))] at hy
    exact le_trans (le_max_right ..) (le_trans (le_max_right ..) (le_trans (le_max_right ..) (le_trans (le_max_right ..) ((le_max_right ..).trans (he.trans (by linarith)))))) -- count
  have hf : Flat.Delay a (X s) 0 := by
    intro i hi
    have he:= ht i; unfold rankDelay at he
    let J:=a.clock.J
    have hJ : J i=J (i+1)-1 ∨ J i=J (i+1) := by
      have ht:= a.fits.mono (show i ≤ i+1 by omega); have hv:=a.fits.stepSlow i; unfold J; omega
    have hx : (X s).Ω (a.clock.J i) ≤ Real.log (Real.log (a.clock.hatBeta i)):= by
      change (X s).Ω (J i) ≤ _
      cases hJ with
      | inl h => rw [h]; exact (le_trans (le_max_right ..) (le_max_left ..)).trans he
      | inr h=> rw [h]; exact (le_trans (le_max_left ..) (le_trans (le_max_right ..) (le_max_right ..))).trans he
    apply hx.trans
    have hu:= Real.add_one_le_exp (Real.log (Real.log (a.clock.hatBeta i)))
    rw [Real.exp_log (Real.log_pos (a.fits.delayed _))] at hu; linarith
  obtain ⟨U,v,v',u,l,c,H'⟩:= Hx s a hg.kernel hg.profile hN _ hf
  have hg' := joined hG hg.atlas (H' H _ hg.atlas) hv
  exact ⟨C,f,T,F,A,hF,hT,hκ ▸ hb,hO,hA,hD,hP,s,p,X s,H,U,v,v',u,l,c,hg.kernel,hg.profile,hg.atlas,hg.attached,fun i=>(le_max_right ..).trans (ht i),H' _ _ hg.atlas,hg'⟩
end YM.RG08.Supplies
