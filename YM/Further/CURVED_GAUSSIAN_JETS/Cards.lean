import YM.Further.CURVED_GAUSSIAN_JETS.Bridge
import YM.Further.CURVED_GAUSSIAN_JETS.Windows
import YM.Progress.STATIONARY_SCENES.SliceGap



/-!
# Bind the Panel & Round line decompositions to the exact ledger

Zeroth-order numerical locality, including an exact ordered-window version of
the difference. Compare a fixed full-key flat Gram with the *completed*
sector Gram; allow two window families (active sector columns and full-key
for log tables). `Fits` can be issued separately for each sector/table;
all costs from Prices so these do NOT have to include period factors if
gap & bill are appropriately funded. We also give a concrete true example
for the stationary *flat uncut* hessian before sector operations. Holes,
cut-path metrics, true covariance choice, tag provenance and local field
jets need their own proofs.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
noncomputable section
namespace YM.Further.CurvedGaussianJets
open Function Filter MeasureTheory Matrix Lattice SectorNext.Vacuum Wilson Tree RG Precision
open Progress.StationaryScenes Bid
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} {Y : Type*} [Fintype Y]

def active {r : Ratio c f} {F : Forest r} (H : Finset F.Free) (G : Gauge) : Bits H G ↪ Key F G :=
  Function.Embedding.inl.trans (tape H G).toEmbedding
lemma active_read {r : Ratio c f} {F : Forest r} (H : Finset F.Free) (K : Table (Bits H G)) :
    (mount H K).submatrix (active H G) (active H G)=K := by
  ext i j
  change Joint.join K (1:Table (H × G.ColorIndex)) ((tape H G).symm ((tape H G) (.inl i))) ((tape H G).symm ((tape H G) (.inl j))) = _
  rw [(tape H G).symm_apply_apply,(tape H G).symm_apply_apply]; rfl
lemma active_pay {r : Ratio c f} {F : Forest r} (H : Finset F.Free) {K : Table (Bits H G)} {a : Key F G → Site n} {p : Prices}
    (h : Fits a p (mount H K)) : Fits (a ∘ active H G) p K := by simpa only [active_read] using h.restrict (active H G)

namespace SliceData
variable (J : ChartRatio G) (R : Rep G f) (P : SliceData G F Y) (B : Table (Key F G)) (p : Prices)
    (a : Key F G → Site n)
    (W : Windows (Key F G)) (T : Windows (Bits P.holds G)) (N : ℕ)
structure Stamped : Prop where
  full (u : Ice P.holds G) : Fits a p (mount P.holds (gram (P.rows u)))
  enough : T.Includes (a ∘ active P.holds G) N
  approx (u) : P.cov u = T.blend (gram (P.rows u))

lemma designs (h : Stamped P p a T N) (hN : p.error N<1) : P.Design where
  pos u := (active_pay _ (h.full u)).pos
  symm u := h.approx u ▸ T.blend_symm _
  short u := by
    rw [h.approx]; exact ⟨p.error N,(p.error_pos _).le,hN,
      Rows.unweighted (T.correction_bill (active_pay _ (h.full u)) h.enough) p.speed_pos.le⟩


end SliceData
open SliceData Push.SectorMeasure Pressure Next.Fluctuations.Sector
variable {x w : ℝ} (D : Allocation G S x w) (J : ChartRatio G)
    (R : Rep G f) (P : Stores S → S.Choices → Config G c → SliceData G F Y) (B : Table (Key F G))
    (G0 : Config G c → ℝ) (p : Prices) (a : Key F G → Site n)
    (T : ∀ H : Finset F.Free, Windows (Bits H G)) {N : ℕ} (h : ∀ s k V, Stamped (P s k V) p a (T (P s k V).holds) N)
    (hb : Fits a p B) (he : p.error N<1)
    {g : ℝ} (hg : 0<g) (hβ : 0<R.beta) (hh : R.beta*g^2=1) (hJ : LocalRatio J)
    (hc : ∀ s k V, Change D J R s k V (P s k V) g)
include hb he h hg hh hJ hc hβ


omit hb he h hg hh hJ hc hβ

lemma key_count : Push.Uniform.Multiplicity (Green.address F (G:=G)) (Fintype.card Axis*Fintype.card G.ColorIndex) := by
  intro x
  rw [← Fintype.card_prod, ← Finset.card_univ]
  let f := fun i : Key F G => (i.1.val.2,i.2)
  refine Finset.card_le_card_of_injOn f (fun _ _=> Finset.mem_univ _) fun i hi j hj hh=> ?_
  have he : Green.address F i=Green.address F j := (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
  exact Prod.ext (Subtype.ext (Prod.ext he (congr_arg Prod.fst hh))) (show (f i).2=(f j).2 from congr_arg Prod.snd hh)


end YM.Further.CurvedGaussianJets
