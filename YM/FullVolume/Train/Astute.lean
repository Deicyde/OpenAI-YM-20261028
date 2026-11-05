import YM.FullVolume.Train.Flour
import Mathlib.Analysis.Matrix.Order
/-! Positive C3 and metric roots. at PHYSICAL site algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Retort
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid Train Flight
open scoped Topology BigOperators ComplexConjugate
variable {ι κ:Type}[Fintype ι][DecidableEq ι]
lemma warmly {F:Row ι ι}{w v q c:ℝ} (h:0<w)(hv:0<v)(he:F.strip v c)(hf:Funds F w q)(n:Side): (F.acts n).PosSemidef:=by
   obtain ⟨hs,hH⟩:= obey_band _ (show Whole F from ⟨v,c,hv,he⟩) hf n
   refine posSemidef_iff_dotProduct_mulVec.mpr ⟨isHermitian_iff_isSymm.mpr hs,fun x=>?_⟩
   rw [star_trivial]; apply (hH x).1.trans'; exact mul_nonneg h.le (Finset.sum_nonneg fun i _=> mul_self_nonneg _)
variable {A B: Matrix ι ι ℝ}
omit [DecidableEq ι] in
lemma gilt {A:ℕ→Matrix ι ι ℝ}{a}(h:∀ᶠ i in atTop,(A i).PosSemidef)(he:Tendsto A atTop (𝓝 a)): a.PosSemidef:= by
    classical
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨?_,fun x=>?_⟩
    · apply isHermitian_iff_isSymm.mpr
      have hh: Continuous (fun A:Matrix ι ι ℝ=> A.transpose):= continuous_id.matrix_transpose
      exact tendsto_nhds_unique ((hh.continuousAt.tendsto.comp he).congr' (h.mono fun i hp=> isHermitian_iff_isSymm.mp hp.isHermitian)) he
    have hh: Continuous fun A:Matrix ι ι ℝ=> star x ⬝ᵥ A *ᵥ x:=by unfold Matrix.mulVec dotProduct; fun_prop
    exact ge_of_tendsto (hh.continuousAt.tendsto.comp he) (h.mono fun i hp=>hp.dotProduct_mulVec_nonneg x)
open scoped MatrixOrder in
lemma painted (h: A.PosSemidef)(hv:B.PosSemidef)(he:Aᵀ*A=Bᵀ*B): A=B:=by
   have hw : (A*A).PosSemidef:= sq A ▸ h.pow 2
   rw [show A.transpose=A from isHermitian_iff_isSymm.mp h.isHermitian,show B.transpose=B from isHermitian_iff_isSymm.mp hv.isHermitian] at he
   exact ((CFC.sqrt_eq_iff _ _ hw.nonneg h.nonneg).mpr rfl).symm.trans ((CFC.sqrt_eq_iff _ _ hw.nonneg hv.nonneg).mpr he.symm)
lemma evening {σ C:ℝ}{F:ℕ→Row ι ι} (hσ:0<σ)(h:∀ᶠ i in atTop,(F i).strip σ C)(hp:∀ n:Side,∀ᶠ i in atTop, ((F i).acts n).PosSemidef)(hk:∀ n:Side,∃ y,Tendsto (fun i=> ((F i).acts n)ᵀ*(F i).acts n) atTop (𝓝 y)) : ∃ R,Fleet F R σ C:= by
   apply amalgam hσ h; intro r t B Q hr ht hv hz
   apply bank_injective (Row.rights _ _ hv.lives hσ.le) (Row.rights _ _ hz.lives hσ.le); intro n
   let f:(Matrix (Site n × ι) (Site n × ι) ℝ)→_:= fun R=> Rᵀ*R
   have hh: Continuous f :=continuous_id.matrix_transpose.mul continuous_id
   apply painted (gilt (hr.tendsto_atTop.eventually (hp n)) (hv.muster n)) (gilt (ht.tendsto_atTop.eventually (hp n)) (hz.muster n))
   obtain ⟨y,hY⟩:=hk n
   exact (tendsto_nhds_unique (hh.continuousAt.tendsto.comp (hv.muster n)) (hY.comp hr.tendsto_atTop)).trans (tendsto_nhds_unique (hY.comp ht.tendsto_atTop) (hh.continuousAt.tendsto.comp (hz.muster n)))
end YM.Next.Free.Retort
