import YM.RG08.Reports.Roads
import YM.RG08.Flat.Entrance

/-!
# Fk order-zero (vacuum Hessian) and the general gate adapter on the common physical selection

Generic gate offers: length lower and beta delay *after* P and all ratios, both can see the UV
receipt's pre-L Sheet/map data; e.g. delay can retain one or more neighbor widths. No absolute or
quantitative asymptotic is claimed for actual Rep on this basis. This selection fixes length/data
delays in advance: no schedule changes by demand after a selection is made. The simple illustration
in `on_same` pays only the flat Hessian gate list.
-/
noncomputable section
namespace YM.RG08.Reports
open Function Set Filter MeasureTheory RG Wilson Lattice Extraction Org Table Spec PhysicalNext PhysicalNext.Repeat.Legato MergeProof Precision
open PhysicalNext.Repeat
open scoped Topology BigOperators Classical ContDiff
open UVExtension RG08 Flat

set_option autoImplicit false
variable {G : Gauge}

/-- Arbitrary delay/gate requests, keep ultraviolet provider endpoints at the same witness.
This can be useful to integrators even if strengthening later formal/local level costs turn out
needed. If geometry/hierarchy is restricted in other ways (e.g. specific power-of-three
factors in a switch proof), this alone doesn't provide that: retains the actual choice from
`Wait.engine`, with requested lower bounds only. -/
theorem paid (hG:G.Simple)(K:KernelChoices)(hk:∀ P:Patch,P.Branches K G)
    (L : Supply.Sheet G → MapPrices → ℕ→ℕ) (U : Supply.Sheet G → MapPrices → (ℕ→ℕ)→ℕ→ℝ) :
    ∃ (C : Family G) (f : Extraction.Order) (T : YM.Table C.book)
      (F : Spec.Final C f T) (A : EveryPhase.Almanac F), C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel = K ∧ Oasis.Floral (hG:=hG) C ∧
      (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
      (∀ d k : ℕ, ∀ᶠ n in atTop,
        ∀ (r : ℕ) (v : Fin r → C.book.Token), (∀ i,(v i).1≤d) → ∃ g, Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed F A ∧ ∃ s P H,ExtraGates L U C s P H := by
  obtain ⟨C,hB,hC,hM,-,hE,hI,hQ,hF,Hq⟩:= with_asks hG K hk L U
  let f := Extraction.Order.full
  obtain ⟨g,Q,N,R,T,E,hA,V,hN⟩:= hF f
  obtain ⟨hs,hD⟩:= hQ (f.refine g) V.copies
  obtain ⟨M,I,h',p⟩:= Acme.emanate (W:=E) hI hG hs hD V hA.clean.ready hA.clean.tilt
  obtain hFinal:= Acme.glistens hC hA.clean.ready hA.clean.tilt p
  obtain ⟨F⟩:=hFinal
  obtain ⟨A,ha⟩:= EveryPhase.all_characters F
  exact ⟨C,_,_,F,A,hM,hC,hB,hE,UVExtension.Reports.useFull hE ⟨F⟩,Poppy.bravo (Oasis.appears hE),ha,Hq⟩

/-- Actual UV/every-phase endpoints in the pinned snapshot, along with quantitative kfalt for the
bulk KERNEL `quadratic` entering its Wilson RG on the same levels (see `Flat.embedded`; attached
also kept explicitly -- that is for R.path and does not assert Affine/fluctuation estimates). -/
theorem on_same (hG:G.Simple)(b : ℝ)(hb:0<b) :
    ∃ (C : Family G) (f : Extraction.Order) (T : YM.Table C.book)
      (F : Spec.Final C f T) (A : EveryPhase.Almanac F), C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty = b ∧ Oasis.Floral (hG:=hG) C ∧
      (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
      (∀ d k : ℕ, ∀ᶠ n in atTop,
        ∀ (r : ℕ) (v : Fin r → C.book.Token), (∀ i,(v i).1≤d) → ∃ g, Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed F A ∧
        ∃ (P : MapPrices) (H:Horizon C.path.levels), H.Suffices P ∧
        (∀ (N i p:ℕ),i≤N → Attached (H.H N i) (C.path.rep N p i).path) ∧
        ∃ w F' a a' d l c,(∀ i,0<w i) ∧ Quorum w F' 0 H a a' d l c := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b hb
  -- Map requests can refer to the same Sheet, independent of UV post-L costs.
  have h (s:Supply.Sheet G) := entrance_gate hG s.kernel s rfl
  choose X E Hx using h
  let D (s:Supply.Sheet G) (_:MapPrices) (_:ℕ→ℕ) (i:ℕ) := Real.exp (max ((X s).Ω i) ((X s).Ω (i-1)))
  obtain ⟨C,f,T,F,A,hF,hT,hκ,hs,hA,hd,hP,s,p,H,hg⟩:= paid hG k hp (fun s _=> E s) D
  let a:= C.path.levels
  have hN (m:ℕ) : E s (a.clock.J (m+1)) ≤ (a.S.block m).val := by rw [← a.fits.sameFactor]; exact hg.cluster _
  have ht : Flat.Delay a (X s) 0 := by
    intro i _
    let j := a.clock.J (i+1)
    have he := hg.payment i
    have hh : Real.exp ((X s).Ω (a.clock.J i)) ≤ a.clock.hatBeta i := by
      apply le_trans _ he; dsimp [D]; apply Real.exp_monotone
      have ht := a.fits.mono (show i ≤ i+1 by omega); have hv := a.fits.stepSlow i
      change _ ≤ max ((X s).Ω (a.clock.J (i+1))) ((X s).Ω (a.clock.J (i+1)-1))
      by_cases hr : a.clock.J (i+1)=a.clock.J i
      · rw [hr]; exact le_max_left ..
      rw [show a.clock.J (i+1)-1=a.clock.J i by omega]
      exact le_max_right ..
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos ((X s).Ω (a.clock.J i))) hh
  obtain ⟨U,v,v',u,l,c,H'⟩:= Hx s a hg.kernel hg.profile hN _ ht
  exact ⟨C,f,T,F,A,hF,hT,hκ ▸ hb,hs,hA,hd,hP, Case.actualPay s p,H,hg.atlas,hg.attached,curve (X s),U,v,v',u,l,c,curve_pos _,H' _ _ hg.atlas⟩
end YM.RG08.Reports
