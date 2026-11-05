import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Quartz
/-!
 # real network receipts → complex current.Same address. ordered payment conversions. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Lattice Set MeasureTheory Wilson RG RG.Supply Input Org Labels
open Source Extra.Histories Next.Foundations
open Push Push.Local Planned.GuardedAtom Planned.AtomRegular WardBin.Lies
open Multi Multi.Vacuum.Jets Multi.Puff
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {n : Side} {m d:ℕ}{F:Frame G d} {R:Rep G n}{T: SectionData F} {A: Hol G}{c:ℝ}
variable {f g : Config G n→ℂ} {B:BudgetPoint}{o:Site n}
private lemma const_castS (h:∀ u,B.dirBound o u→ ‖leftDerivs f (List.replicate d u) 1‖ ≤ c)(_hw:0≤c)(hp:Local.Chart d f 1) :
    ∀ v: Fin d→ Directions G n,(∀ i,B.dirBound o (v i)) → ‖iteratedFDeriv ℝ d (f ∘ increment 1) 0 v‖ ≤ polarCost d * c:=by
    let U:=amp (G:=G) B o; let q:= f ∘ increment (1:Config G n); let F':= iteratedFDeriv ℝ d q 0; let P:=F'.compContinuousLinearMap (fun _=> U)
    have h':ContDiffAt ℝ (↑d) q 0:=hp
    have hS : Tensor.Sym P:=fun v s => Analysis.sym_Jet h' (U ∘ v) s
    intro v hv; let w i:=suppress B o (v i)
    have he i : ‖w i‖ ≤ 1:= by apply (amp_fits B o).mp; exact (amp_suppress B o (v i)).symm ▸ hv i
    have ht (x) (hx:‖x‖ ≤ 1) : ‖Tensor.diagonal P x‖ ≤ c:=by
       change ‖Tensor.diagonal F' (U x)‖ ≤ c; rw [← iteratedDeriv_on_line h' (U x)]; change ‖iteratedDeriv d (fun t : ℝ => f (increment 1 (t • U x))) 0‖ ≤ _
       rw [← leftDerivs_diag, zero_smul, Work.G07.at_zero_increment]; exact h _ ((amp_fits ..).mpr hx)
    rw [show iteratedFDeriv ℝ d (f ∘ increment 1) 0 v=P w from congr_arg F' (funext fun i=> (amp_suppress _ _ (v i)).symm)]
    exact polarizes hS ht _ he

def gaugeMeter (d:ℕ) := 1+∑ i∈Finset.range (d+1),polarCost i
lemma horizon : 1 ≤ gaugeMeter d:=le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _=>zero_le_one.trans (polar_one _)))
lemma speedTest (A:Hol G)(s:Support n)(p:Probe G d) (hf:Local.Chart d f 1)(hg:Local.Chart d g 1)
    (h:∀ l:List (Directions G n),l.length ≤ d→ (∀ v∈l, B.dirBound o v) → ‖leftDerivs f l 1-leftDerivs g l 1‖≤c): IdentityTest A o s B f (g ∘ increment 1) p (gaugeMeter d*c):=by
   have hw : ‖f 1-g 1‖ ≤ c:= h [] (Nat.zero_le _) (by simp); have ht:0≤c:= (norm_nonneg _).trans hw
   let Zℓ:=f-g; have hX:Local.Chart d Zℓ 1:=hf.sub hg
   refine ⟨?_,fun _=>hg, fun _ m hm w hv=>?_⟩
   · rw [Function.comp_apply,Work.G07.at_zero_increment]; exact hw.trans (le_mul_of_one_le_left ht horizon)
   have hp : (m:ℕ∞ω) ≤ (d:ℕ∞ω):=Nat.cast_le.mpr hm; have hL:ContDiffAt ℝ (d:ℕ∞ω) (f ∘ increment 1) 0:=hf; have hQ:ContDiffAt ℝ (d:ℕ∞ω) (g ∘ increment 1) 0:=hg
   have he(v)(hh:B.dirBound o v) := h (List.replicate m v) (List.length_replicate.trans_le hm) (fun k hL=>(List.mem_replicate.mp hL).2 ▸ hh)
   have hb(v)(hh : B.dirBound o v) : ‖leftDerivs Zℓ (List.replicate m v) 1‖ ≤ c:= by unfold Zℓ; rw [redacted (into d f hf) (into d g hg) (List.length_replicate.trans_le hm)]; exact he v hh
   have hy: polarCost m ≤ gaugeMeter d:= (Finset.single_le_sum (fun i _=> zero_le_one.trans (polar_one i)) (show m∈Finset.range (d+1) from Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)
   have h : iteratedFDeriv ℝ m (Zℓ ∘ increment 1) 0= _:= iteratedFDeriv_sub_apply (hL.of_le hp) (hQ.of_le hp)
   have H:= le_trans (const_castS hb ht ((show ContDiffAt ℝ d (Zℓ ∘ increment 1) 0 from hX).of_le hp) w (fun i=> (hv i).1)) (mul_le_mul_of_nonneg_right hy ht)
   rw [h] at H; exact H

lemma cleared {a b x y: Config G n →ℝ}(hf:Germ d a 1)(hx:Germ d b 1)(hy:Germ d x 1)(hz:Germ d y 1)(c v:ℝ) (l : List (Directions G n))(hl:l.length ≤ d)(u:ℂ) (he:‖leftDerivs a l 1-leftDerivs x l 1‖ ≤ c)(hq:‖leftDerivs b l 1-leftDerivs y l 1‖ ≤ v) :
    ‖leftDerivs (u • (Complex.ofReal ∘ a + Complex.I • (Complex.ofReal ∘ b))) l 1-leftDerivs (u • (Complex.ofReal ∘ x + Complex.I • (Complex.ofReal ∘ y))) l 1‖≤ ‖u‖*(c+v):=by
  let W(a:Config G n→ℝ):=Complex.ofReal ∘ a
  have hh(a:Config G n→ℝ)(h:Germ d a 1):Multi.Puff.Crest d (W a) 1:= into _ _ (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (show Push.Local.Chart d a 1 from h))
  have hv(a b:Config G n→ℝ)(hc:Germ d a 1)(hb:Germ d b 1): leftDerivs (u • (W a+Complex.I • W b)) l 1= u * (((leftDerivs a l 1:ℝ):ℂ)+Complex.I*((leftDerivs b l 1:ℝ):ℂ)):=by rw [scaled_left,Crest.sum_at l hl 1 (hh a hc) (into d (Complex.I • W b) ((hh b hb).germ.const_smul Complex.I)),scaled_left]; rw [show leftDerivs (W a) _ _= _ from Push.Local.left_linear Complex.ofRealCLM l (show Local.Chart d a 1 from hc) hl, show leftDerivs (W b) _ _= _ from Push.Local.left_linear Complex.ofRealCLM l (show Local.Chart d b 1 from hb) hl]; rfl
  change ‖leftDerivs (u • (W a+ _)) _ _ - leftDerivs (u • (W x+ _)) _ _‖ ≤ _
  rw [hv a b hf hx,hv x y hy hz, ← mul_sub,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg u)
  set A:= leftDerivs a l 1; set B:= leftDerivs b l 1; set X:=leftDerivs x l 1; set Y:=leftDerivs y l 1
  rw [show (A:ℂ)+Complex.I*B-((X:ℂ)+Complex.I*Y)= ↑(A-X) + Complex.I*↑(B-Y) from by push_cast; ring]; refine (norm_add_le ..).trans ?_
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Complex.norm_I,one_mul]; exact add_le_add he hq
end YM.PhysicalNext.Repeat.Cub
