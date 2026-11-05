import YM.Planned.PRIMARY_INTEGRAL_295.Density
/-!
# Finite numerical slot fibers despite infinite address input

Group only to get norm/pass-derivative bounds on the same unforced
trajectory rows before Budget. No identification of
addresses at gas/source combinatorial ledgers, and no ignoring tag labels.
At true cut replace terms by zero. Count polynomial weights cost uniform
suppliersΛ before consumption. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Festoons
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform   Density 
open Next.Fluctuations
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Gauge} {c f : Side} {S:StepData c f}

-- slot windows literal. all axes 8.
def alphabet := Finset.univ.image fun i:Axis×Bool=>Lattice.Step.mk i.1 i.2
def natives : ℕ→ Finset Walk
  | 0=> {[]}
  | n+1 => insert [] ((alphabet.product (natives n)).image (fun i=> i.1::i.2))
lemma spelling (n:ℕ) (s:Walk):s∈natives n ↔ s.length≤n := by
   induction n generalizing s with
   | zero => simp [natives]
   | succ n ih =>
     cases s with
     | nil => simp [natives]
     | cons d t =>
       have hd:d∈ alphabet:= Finset.mem_image_of_mem (fun i:Axis×Bool=>Lattice.Step.mk i.1 i.2) (Finset.mem_univ (d.dir,d.neg))
       simp [natives,Finset.mem_product, ih,hd]

def garth (d n:ℕ) := ((natives n).biUnion fun w=> Finset.univ.image (fun p=>Slot.mk w p)).filter (fun s=>s.length*d≤ n)
lemma charge (s:Slot) (d n:ℕ)(hd:0<d):s∈garth d n ↔ s.length * d ≤ n:=by
   refine ⟨fun h=> (Finset.mem_filter.mp h).2,fun h=>?_⟩
   refine Finset.mem_filter.mpr ⟨?_,h⟩
   refine Finset.mem_biUnion.mpr ⟨s.walk,(spelling n _).2 ?_,Finset.mem_image_of_mem (Slot.mk s.walk) (Finset.mem_univ s.plaq)⟩
   unfold Slot.length at h; exact le_trans ((by omega:s.walk.length≤s.walk.length+4).trans (le_mul_of_one_le_right (Nat.zero_le _) hd)) h

noncomputable def echo (p:PathData G)(i:PlaqAxes)(s:Slot):ℕ→ℝ := fun n=> if (p.row i n).2=s then (p.row i n).1 else 0
def chip (p:PathData G)(i:PlaqAxes)(s:Slot):= ∑' n,echo p i s n

def shelf (p:PathData G)(i:PlaqAxes)(d n:ℕ) (f:Slot→E) := fun k:ℕ=>
    let c:=p.row i k
    if c.2.length*d≤n then c.1 • f c.2 else 0

def clamp (p:PathData G)(i:PlaqAxes)(d n:ℕ) (f:Slot→E) := ∑ s∈garth d n, chip p i s • f s

namespace Price
variable (p:PathData G) {σ C Λ : ℝ}{A:Clip} (h:p.Bounds A σ C Λ)
include h
lemma clips (i:PlaqAxes):Summable (fun k=> ‖(p.row i k).1‖) :=by
   refine Summable.of_norm_bounded (h.rows i).2.1 (fun k=>?_); rw [norm_norm,Real.norm_eq_abs];
   apply le_mul_of_one_le_right (by positivity); exact Real.one_le_exp (mul_nonneg h.width.le (by positivity))
lemma echoed (i:PlaqAxes)(s:Slot): Summable (fun k=>‖echo p i s k‖) := by
   refine Summable.of_norm_bounded (clips p h i) (fun k=>?_); unfold echo; split <;> simp
lemma cooked (i:PlaqAxes)(d n:ℕ): (∑ s∈garth d n, |chip p i s| * Real.exp (σ*s.length)) ≤ C:= by
   let g(s:Slot)(k:ℕ):= ‖echo p i s k‖*Real.exp (σ*s.length)
   let B:=garth d n
   have he(s): Summable (g s) := (echoed p h i s).mul_right _
   have hv(s): |chip p i s| *Real.exp (σ*s.length) ≤ ∑' k,g s k:= by
     unfold chip g; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (echoed p h i s)) (Real.exp_pos _).le
   apply (Finset.sum_le_sum (fun i _=>hv i)).trans; rw [← Summable.tsum_finsetSum (fun i _=> he i)]; refine le_trans ?_ (h.rows i).2.2
   apply (summable_sum (fun s (_:s∈B)=>he s)).tsum_le_tsum _ (h.rows i).2.1 -- theorem name?
   intro k; simp only [g,echo]; let s:=(p.row i k).2
   simp_rw [apply_ite norm, norm_zero,ite_mul,zero_mul]; simp only [Finset.sum_ite_eq]; split
   · exact le_rfl
   positivity

variable [CompleteSpace E]
omit [CompleteSpace E] in
lemma wired (i:PlaqAxes) (f:Slot→E)(d n:ℕ)(hd:0<d): Summable (shelf p i d n f) ∧ (∑' k,shelf p i d n f k) = clamp p i d n f:=by
   let U:=garth d n; let g(s:Slot)(k:ℕ):= echo p i s k • f s
   have he(s):Summable (g s):=(echoed p h i s).of_norm.smul_const (f s)
   have hv: shelf p i d n f=fun k=>∑ s∈ U,g s k:=by
      funext k; unfold shelf g echo; simp_rw [ite_smul,zero_smul]; simp [U,charge _ _ _ hd]
   rw [hv]; refine ⟨?_,?_⟩
   · exact summable_sum (fun i (_:i∈U)=> he i)
   rw [Summable.tsum_finsetSum (fun s _=>he s)]; refine Finset.sum_congr rfl fun i' _=>?_
   exact ((echoed p h i i').of_norm.hasSum.smul_const (f i')).tsum_eq

lemma tail_cost (i:PlaqAxes) (f:Slot→E)(d n:ℕ)(hd:0<d)(L:ℝ)(hL:∀ s, ‖f s‖ ≤ L):
     let F(k:ℕ):= (p.row i k).1 • f (p.row i k).2
     Summable F ∧ ‖(∑' j,F j)-clamp p i d n f‖ ≤ C*Real.exp (-(σ/d)*n)*L:=by
   intro F; let c:= Real.exp (-(σ/d)*n)
   have he:0 ≤ c:=(Real.exp_pos _).le; have hm:0≤L:=(norm_nonneg (f (p.row i 0).2)).trans (hL _)
   have hh(k): ‖F k‖ ≤ |(p.row i k).1| *L:=by unfold F; rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hL _) (by positivity)
   have hf:Summable F:=Summable.of_norm_bounded ((clips p h i).mul_right L) hh
   obtain ⟨hk,hv⟩:= wired p h i f d n hd; refine ⟨hf,?_⟩; rw [←hv,← hf.tsum_sub hk]; let g:=shelf p i d n f
   let z(k:ℕ):= |(p.row i k).1| *Real.exp (σ*(p.row i k).2.length)*(c*L)
   have hz:Summable z:=(h.rows i).2.1.mul_right _
   have hy (k:ℕ): ‖F k-g k‖ ≤ z k := by
      unfold g shelf; dsimp only
      split <;> rename_i hk
      · change ‖F k-F k‖ ≤ _; rw [sub_self,norm_zero]; unfold z; positivity
      rw [sub_zero]; apply (hh k).trans
      have ha:1≤ Real.exp (σ*(p.row i k).2.length)*c:=by
         unfold c; rw [←Real.exp_add]; apply Real.one_le_exp
         have hp:0<(d:ℝ):=Nat.cast_pos.mpr hd
         have hx : (n:ℝ) ≤ (p.row i k).2.length*d:=by exact_mod_cast Nat.le_of_lt (lt_of_not_ge hk)
         have hu := mul_le_mul_of_nonneg_left hx (show 0 ≤ σ/d from div_nonneg h.width.le hp.le)
         have hm := div_mul_cancel₀ σ hp.ne'
         linarith [congr_arg (· * (↑(p.row i k).2.length:ℝ)) hm]
      refine (le_mul_of_one_le_right (by positivity) ha).trans_eq ?_; unfold z; ring
   have hx: Summable (fun k=>‖F k-g k‖):=Summable.of_norm_bounded hz (fun k=>by rw [norm_norm]; exact hy k)
   apply (norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum hy hz).trans ?_)
   unfold z; rw [tsum_mul_right,mul_assoc]; exact mul_le_mul_of_nonneg_right (h.rows i).2.2 (by positivity)
end Price

section
variable (p:PathData G) {σ C Λ:ℝ}{A:Clip} (h:p.Bounds A σ C Λ)
include h
lemma clipped_short (i:Cell c) (V:Config G c) (n d:ℕ)(hd:0<d): Pressure.shorten p n d V i=clamp p i.2 d n (fun s=>s.atSite V i.1):=(Price.wired p h i.2 (fun s=>s.atSite V i.1) d n hd).2
lemma clipped_mb (K:Core G S)(U V:Config G f)(i:Cell f)(hh:K.tube.up=p): (∑' j,K.mbTerm U V i j) = clamp p i.2 1 K.R (fun s=> kink s U V i.1):=by
    have he:K.mbTerm U V i= shelf p i.2 1 K.R (fun s=> kink s U V i.1):=by unfold mbTerm shelf; rw [hh]; simp only [mul_one]
    rw [he]; apply (Price.wired p h _ _ 1 _ (by norm_num)).2
end
end YM.Planned.PrimaryIntegral295.Festoons
