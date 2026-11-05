import YM.Push.FINITE_DETECTION.Leading
import YM.Work.G05.Taylor
import YM.Pert.Fourier.Cellular
/-!
# Smooth probes and budgets on the native centered preimage cell

Real finite-volume tests involve no torus chart wrap outside this exact address
unrolling. Directions are polynomial tests here; slope later (derivatives as
functionals in native coordinates, retaining all supports).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Native
open Tensor Analysis Function Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

abbrev box:Set E4:= Pert.Cellular.cells
lemma box0 : (0:E4)∈box:= fun i=> by rw [PiLp.zero_apply]; norm_num
lemma box_convex : Convex ℝ box:= by
    intro x hx y hy a b ha hb h
    refine fun i=> ?_; rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply]; simp only [smul_eq_mul]
    apply le_trans (abs_add_le ..); rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    grw [hx i,hy i]; rw [← add_mul,h,one_mul]

abbrev probes: Submodule ℂ (E4→ℂ) := {
    carrier:={t|ContDiff ℝ ∞ t}
    zero_mem':= (contDiff_const (c:=(0:ℂ)) (E:=E4) (𝕜:=ℝ) (n:=∞))
    add_mem' := fun {a b} ha hb => ContDiff.add (f:=a) (g:=b) (show ContDiff ℝ ∞ a from ha) (show ContDiff ℝ ∞ b from hb)
    smul_mem' := fun c a ha=> ContDiff.const_smul (f:=a) c (show ContDiff ℝ ∞ a from ha) }
abbrev Body:=↥probes
abbrev PulseC:= Body →ₗ[ℂ]ℂ
lemma body_smooth (x:Body) (i:ℕ) : ContDiff ℝ i x.val:=by
  have h:ContDiff ℝ ∞ x.val:= x.property
  exact h.of_le (WithTop.coe_le_coe.mpr le_top)

def pull (δ:E4)(r:ℝ) : Body →ₗ[ℂ] Body where
  toFun p:=⟨fun x=> p.val (δ+r • x), ContDiff.comp (g:=p.val) (show ContDiff ℝ ∞ p.val from p.property) ((contDiff_const (c:=δ)).add (ContDiff.const_smul r contDiff_id))⟩
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

lemma pulled (δ:E4)(r:ℝ)(f:Body)(i:ℕ)(x:E4): iteratedFDeriv ℝ i (pull δ r f).val x=r^i • iteratedFDeriv ℝ i f.val (δ+r • x):=by
   let g(z):=f.val (δ+z); change iteratedFDeriv ℝ i (fun x=> g (r • x)) x=_
   rw [iteratedFDeriv_comp_const_smul r (show ContDiff ℝ i g from (body_smooth f i).comp (contDiff_const.add contDiff_id))]
   simp only [g]; rw [iteratedFDeriv_comp_add_left]

def Cap (d:ℕ)(B:Body)(c:ℝ):Prop:=∀ i≤d,∀ x∈box, ‖iteratedFDeriv ℝ i B.val x‖≤c
lemma Cap.nonneg {d:ℕ}{f:Body}{c:ℝ}(h:Cap d f c): 0≤c:=le_trans (norm_nonneg _) (h 0 (Nat.zero_le _) 0 box0)
lemma cap_aff (δ:E4){r:ℝ} (hr:0≤r)(hv:r≤1)(ht:MapsTo (fun x=>δ+r • x) box box) {f:Body} {d:ℕ} {c:ℝ}(hc:Cap d f c):Cap d (pull δ r f) c:=by
    intro i hi x hx
    rw [pulled,norm_smul,Real.norm_of_nonneg (pow_nonneg hr _)]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr hv)) (hc i hi _ (ht hx))
lemma Cap.increase {d:ℕ}{f:Body}{c b:ℝ}(h:Cap d f c) (hb:c≤b):Cap d f b:=fun i hi z hz => le_trans (h i hi z hz) hb
lemma Cap.plus {d:ℕ}{f g:Body}{c b:ℝ}(h:Cap d f c)(H:Cap d g b):Cap d (f+g) (c+b):= by
   intro i hi z hz; rw [show (f+g).val=f.val+g.val from rfl, iteratedFDeriv_add (body_smooth ..) (body_smooth ..), Pi.add_apply]; exact (norm_add_le ..).trans (add_le_add (h _ hi z hz) (H _ hi z hz))
lemma Cap.minus {d:ℕ}{f g:Body}{c b:ℝ}(h:Cap d f c)(H:Cap d g b):Cap d (f-g) (c+b):= by
   intro i hi z hz; rw [show (f-g).val=f.val-g.val from rfl, iteratedFDeriv_sub (body_smooth ..) (body_smooth ..), Pi.sub_apply]; exact (norm_sub_le ..).trans (add_le_add (h _ hi z hz) (H _ hi z hz))
lemma Cap.cost (f:Body)(d:ℕ): ∃ c>0,Cap d f c:=by
   have hB(i:Fin (d+1)):=Pert.Cellular.cells_compact.exists_bound_of_continuousOn ((body_smooth f i.val).continuous_iteratedFDeriv (m:=i.val) (by rfl)|>.continuousOn)
   choose C h using hB; have h0(i:Fin (d+1)):0 ≤ C i:= (norm_nonneg _).trans (h i 0 box0)
   let c:= 1+ ∑ i,C i; refine ⟨c,add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _=> h0 i),fun i hi x hx => ?_⟩
   exact le_trans (h ⟨i,Nat.lt_add_one_of_le hi⟩ x hx) ((Finset.single_le_sum (fun i _=>h0 i) (Finset.mem_univ _)).trans (le_add_of_nonneg_left zero_le_one))

lemma Cap.from_high {f:Body}{d s:ℕ} {c:ℝ}(hc:0≤c) (hx:d<s)(h:∀ i≤d,iteratedFDeriv ℝ i f.val 0=0)(ht:∀ i, d < i → i ≤ s → ∀ x∈box,‖iteratedFDeriv ℝ i f.val x‖ ≤ c): Cap s f c:=by
     intro i hi
     have hv(k:ℕ) (hk:k≤d+1) : ∀ x∈box,‖iteratedFDeriv ℝ (d+1-k) f.val x‖≤c:=by
        induction k with
        | zero => exact ht _ (Nat.lt_succ_self _) (by omega)
        | succ k ih =>
          let i:= d+1-(k+1); have he:i+1=d+1-k:=by unfold i; omega
          have hr x: DifferentiableAt ℝ (iteratedFDeriv ℝ i f.val) x:=(body_smooth f (i+1)).contDiffAt.differentiableAt_iteratedFDeriv (m:=i) (Nat.cast_lt.mpr i.lt_succ_self)
          intro x hx; have hn:‖iteratedFDeriv ℝ i f.val x - iteratedFDeriv ℝ i f.val 0‖ ≤ c*‖x-0‖:=by
             refine box_convex.norm_image_sub_le_of_norm_fderiv_le (fun x _=>hr x) (fun z hz => norm_fderiv_iteratedFDeriv.trans_le ?_) box0 hx
             rw [he]; exact ih (by omega) z hz
          rw [h i (by dsimp [i]; omega),sub_zero, sub_zero] at hn
          exact hn.trans (mul_le_of_le_one_right hc (Pert.Cellular.cells_bd hx))
     by_cases hp:i ≤ d
     · have he:d+1-(d+1-i)=i:=by omega
       exact he ▸ hv (d+1-i) (by omega)
     exact ht i (Nat.gt_of_not_le hp) hi

end YM.RG05Readout.Native
