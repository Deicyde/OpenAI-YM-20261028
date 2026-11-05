import YM.RG08.Carrel.Cost
import YM.RG08.Reports.Receipt

/-!
# Stem quadratic packets on cover, Haar colors common. Shift covariant. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Cast
open Lattice Laurent Forms Pert.Bulk Isles Packets Carrel Filter Finset Function Matrix RG
open Anchor Rudder Rudder.Symmetry Exterior Stationary Bloch RG08.Flat
open scoped Topology ContDiff Classical BigOperators ENNReal Matrix
variable {I J:Type}{G:Gauge}{n:ℕ}{P:Side}
variable (G)(D:Kernel (TypeFace n) (TypeFace n))

local notation "o" => (0 : Fin 2)
local notation "u" => (Fin.succ (0:Fin 1))

def spur :Flake 2 (Mix G.ColorIndex n):=fun x=> if (x o).2.2=(x u).2.2 then
   D ((x o).1,(x o).2.1) ((x u).1,(x u).2.1) else 0
def beam:Rudder.Raw G.ColorIndex 2:= Anchor.extend n (spur G D)
variable {G D} {σ p :ℝ}
lemma beam_sub (G:Gauge)(D V:Kernel (TypeFace n) (TypeFace n)): beam G (D-V)=beam G D-beam G V:=by
 funext x; unfold beam Anchor.extend spur;by_cases h:permitted Cover G.ColorIndex n x
 · simp only [h,↓reduceDIte,Pi.sub_apply];split_ifs <;> simp
 simp [h]
lemma spur_path (h:city 1 D):Cohort (spur G D):=by
 intro q x; unfold spur
 by_cases hh:(x o).2.2=(x u).2.2
 · rw [if_pos (show (sway q x o).2.2=(sway q x u).2.2 from hh),if_pos hh]
   simpa [sway,Packets.pass,show ((1:Side).val)=1 from rfl] using h ((x o).1,(x o).2.1) ((x u).1,(x u).2.1) q
 rw [if_neg (show (sway q x o).2.2≠(sway q x u).2.2 from hh),if_neg hh]
private lemma twin (d:Ground I)(X:Tape 2 I):d.radius X≤ d.span (X o) (X u):=by
 apply d.radius_le _ (d.nn ..);intro i j;fin_cases i <;> fin_cases j <;> first
  | exact le_rfl
  | apply le_of_eq; exact d.left ..
  | exact (d.stay _).le.trans (d.nn ..)
lemma from_row (D:Kernel I J)(h:city 1 D)(H:RowCost σ 1 D p):ColCost σ 1 D p:=by
 intro i z
 let f(x:Cover):=bill (D (0,i) (z.1-x,z.2)) (σ*sep 0 (z.1-x))
 apply le_trans (b:=∑' x,f x)
 · apply ENNReal.tsum_le_tsum;intro x;unfold f
   have hi:=h (0,i) (z.1-x,z.2) x
   simp only [Packets.pass,show (1:Side).val=1 from rfl,one_smul,sub_add_cancel,zero_add] at hi
   rw [delta_one,←hi];unfold sep;rw [show (x-z.1)=(0-(z.1-x)) by abel]
 let q:Equiv.Perm Cover:=⟨fun x=>z.1-x,fun x=>z.1-x,sub_sub_cancel _,sub_sub_cancel _⟩
 unfold f
 rw [show (∑' x,bill (D (0,i) (z.1-x,z.2)) (σ*sep 0 (z.1-x)))=(∑' y,bill (D (0,i) (y,z.2)) (σ*sep 0 y)) from q.tsum_eq (fun v =>bill (D (0,i) (v,z.2)) (σ*sep 0 v))]; simpa only [delta_one] using H (0,i) z.2

abbrev tax (G:Gauge)(n:ℕ):ℝ:= (Fintype.card (Kind G.ColorIndex n):ℝ)
lemma spur_cost (h:RowCost σ 1 D p)(hh:ColCost σ 1 D p)(_hp:0≤p)(he:0≤σ):Held (carpet _) σ (tax G n*p) (spur (n:=n) G D):=by
 rw [ensign]
 let swapR:=Equiv.swap o u
 -- row computation for any orientation then permute
 have h0 (e:Equiv.Perm (Fin 2))(K:Kernel (TypeFace n) (TypeFace n))(hk: RowCost σ 1 K p)(ht:woven (spur G D) e=spur G K)
    (i:Fin 2)(hi:e i=o)(z:Mix G.ColorIndex n):∑' x,Forms.row (mark (carpet _) σ (spur G D)) i z x≤ENNReal.ofReal (tax G n*p):=by
      let d:= carpet (Kind G.ColorIndex n)
      have hEq(X:Tape 2 _):Forms.row (mark d σ (spur G D)) i z (twist e X)=Forms.row (mark d σ (spur G K)) o z X:=by
         have hg:(X ∘ e) i=z ↔ X o=z:=by rw [Function.comp_apply,hi]
         unfold Forms.row mark;by_cases hx:(X ∘ e) i=z
         · rw [if_pos (show twist e X i=z from hx), if_pos (hg.mp hx),show d.radius (twist e X)=d.radius X from Ground.radius_perm .., show spur G D (twist e X)=spur G K X from congrFun ht X]
         rw [if_neg (show twist e X i≠z from hx),if_neg (mt hg.mpr hx)]
      rw [←(twist e).tsum_eq]
      change (∑' c, Forms.row (mark d σ (spur G D)) i z (twist e c))≤_
      simp_rw [hEq];rw [ensign_face]
      rw [← (Equiv.funUnique (Fin 1) (Market (Kind G.ColorIndex n))).symm.tsum_eq,ENNReal.tsum_prod',ENNReal.tsum_comm,tsum_fintype]
      unfold tax;rw [ENNReal.ofReal_mul (by positivity),show ENNReal.ofReal (Fintype.card (Kind G.ColorIndex n):ℝ) * _=∑ _ : Kind G.ColorIndex n, ENNReal.ofReal p from ?_]
      · apply sum_le_sum;intro a _; cases hz:z with| mk pZ f=>cases f with|mk f c=> cases a with|mk g c'=>
          apply le_trans _ (hk (pZ,f) g)
          apply ENNReal.tsum_le_tsum;intro y
          -- shrink diam
          unfold mark; change bill (if c=c' then _ else 0) (σ*d.radius _) ≤ _ -- inequality
          change bill (if c=c' then K (pZ,f) (y,g) else 0) _ ≤ _
          rw [delta_one];apply bill_mono
          · split_ifs <;> simp
          apply mul_le_mul_of_nonneg_left _ he
          exact twin d _
      simp
 intro i z
 fin_cases i
 · exact h0 (Equiv.refl _) D h rfl o rfl z
 -- use swap with transposed kernel
 let K:= Function.swap D
 have hE:woven (spur G D) swapR=spur G K:= by funext x;simp [Function.comp_apply,K,Function.swap,spur,woven,swapR,eq_comm]
 apply h0 swapR K (fun z i=> by simpa [K,Function.swap,delta_one,sep_comm z.1] using hh i z) hE u (Equiv.swap_apply_right ..) z
end YM.RG08.Cast
