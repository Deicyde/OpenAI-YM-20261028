import YM.MergeProof.Maid
import YM.MergeProof.Newell
import YM.MergeProof.Stove
import YM.Next.RANK.HomeSync


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank  Spindle Extra.Multi Motion Local
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V] {G:Gauge}(C:Family G)(N k m p d:ℕ)(v:C.label d)
section
local notation "μ"=> winter G d
local notation "P"=> C.path.levels
local notation "σ"=> C.S
def plumR (r:ℝ)(i:ℕ):ℝ:= C.S.a i^d*Mix.width C r (2*winter G d) i
lemma stockpit (r:ℝ)(hr:0 < r):0<plumR C d r k:=mul_pos (pow_pos (C.S.a_pos k) _) (width_pos C k hr _)
lemma stocking (r:ℝ)(hr:0 < r)(hk:C.ref d ≤ k)(hn:k≤N)(h:C.Makes)(hv:(C.labels.level d).coeffSize v≤r): plumR C d r k*moneys C d k N p v ≤ fly C.path.levels d k:=by
    have hp := pays_coord C N p k hr (2* μ) h v hv hk hn
    let V:ℝ:= Mix.width C r (2*μ) k; let a:= σ|>.a k
    have ha:0<a:= C.S.a_pos k
    let x:= (P)|>.clock.hatBeta k
    have hx: (gHat C k)^(2*μ)=fly C.path.levels d k:=by
       have he:0<x := lt_trans zero_lt_one (C.path.levels.fits.delayed k)
       have hp:(gHat C k)^2=x⁻¹:=by change Vac.Numbers.Hat x ^2=_; unfold Vac.Numbers.Hat; rw [inv_pow,Real.sq_sqrt he.le]
       rw [pow_mul,hp];exact inv_pow x _ -- rw silly
    let X:= (C.labels.level d).coeffSize (coord C N p k v).x
    show _≤ _; refine (le_of_eq (b:=V*(col C k*X)) ?_).trans (hp.trans_eq hx)
    unfold moneys Next.Rank.Spindle.paid Price.awake; rw [Size.smul]; change a^d*V* (col C k*(‖alto C.path k d‖ * X))=_; rw [alto_norm]; change a^d*V* (col C k*((a^d)⁻¹* X))=_; field_simp
lemma fly_le : fly C.path.levels d k≤1:=inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt (C.path.levels.fits.delayed k)))
end
section
variable {o:∀ i:ℕ,V→Site (C.side i p)}(s:V→ C.label d) (t:V→Motion) {w:V→ℝ}{a:ℝ}
lemma punctual (h:C.Makes) (hk:C.ref d≤k) (hv:k ≤ N)(hV:∀ i,w i*moneys C d k N p (s i) ≤ a)(hw:∀ i,0 < w i) : Vault w (fun i=>indexX C d N p (s i) (fun j=>o j i) (t i) k) (fun i=>Ktone C d N p (s i) (fun j=>o j i) (t i) k) (3*a) a:=by
    have hg(i:V)(U):= scratch C (s i) k p N (t i) (fun j=>o j i) h hk hv U
    constructor
    · intro i U; apply (mul_le_mul_of_nonneg_left (hg _ U|>.1) (hw i|>.le)).trans; rw [mul_left_comm (w i) 3]; exact mul_le_mul_of_nonneg_left (hV i) (by norm_num)
    intro i U; rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left ((hg i U).2) (hw i|>.le)).trans (hV i)
end
end YM.MergeProof.Accent
