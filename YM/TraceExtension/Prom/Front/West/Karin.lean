import YM.MergeProof.West.Karin
import YM.TraceExtension.Prom.Front.West.Canvas
import YM.TraceExtension.Prom.Front.West.Leet
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.Rose
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Station
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition
variable {G:Gauge}{N n p k q i d D:ℕ} {C:Family G} {R:Lead G C.S p}
   {b:ℝ} {c:Course C N p k}{x:Points n}{hk:i<k}{h:middleSky C.path.levels b k ≤ i}
   {T τ U ε g B Y L} (E:StageNowSky (d:=d) c R x b hk h q T τ U ε)

lemma plankSky (s : ℂ) (X' : (j : Fin E.count) → (E.tag j).Θ →ℂ) : plaidFtSky E (fun j z=>s * X' j z)=s*plaidFtSky E X':= by
    unfold plaidFtSky mixedFtSky; rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro i _; letI:= (E.tag i).M; dsimp only; rw [integral_const_mul,mul_left_comm]

variable (S:List (ℝ × List (modes (Fin n))))
variable (P:modes (Fin n) → poly (Chamber G C.S (i+1) p))
def traySky := fun (j:Fin E.count) z=> honors S (p_lanterSky E (offerNowSky E P) j z).part
def platterSky := dot ((Ship.yardSky C b c.allow p).hand T.1) (e_leganceSky b c x hk h T U ((R i).read (honors S P)))

variable (hP : ∀ u,P u ≠ 0 → ∃ i : ViewFt C k b p d x hk,i.val.val=u)
variable (hx:roomTestSky C.path.levels b k p d q) (t:Metal b c R hk ε τ g B Y L) (Hv:Healthy g (d_olmSky x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U) (he: 0 < ε)(he':ε≤1)
   {r:ℝ} (hr:0≤r)
variable (H:∀ i, Poetic (P i)) (hs:∀ i,totalDegree (P i)≤ D) (hu:∀ i,coin (P i)≤ r) (hp:∀ u : Manner n,∀ i'∈(P u.val).vars,spotFt b (i+1) d (show i+1≤k from hk) x u i' (C:=C))
include hP hx t Hv he he' hr H hs hu hp
lemma sweepSky (hS: ∀ t∈S,∀ i∈t.2,i.val ⊆ T.2.val.val.val) :
   (∀ j,letI:= (E.tag j).M; Integrable (traySky E S P j) (E.tag j).μ) ∧
    ‖plaidFtSky E (traySky E S P)-platterSky (c:=c) (R:=R) (hk:=hk) (h:=h) (T:=T) (U:=U) S P‖ ≤ grantS S B ε r D:= by
   let A:= fun x=> platterSky (c:=c) (R:=R) (hk:=hk) (h:=h) (T:=T) (U:=U) x P
   let K:= (Ship.yardSky C b c.allow p).hand T.1; let e:= e_leganceSky b c x hk h T U
   induction S with
   | nil=>
     change _ ∧ ‖plaidFtSky E (fun _ _=>0)-dot K (e ((R i).read 0))‖≤ 0
     refine ⟨fun j=>?_,?_⟩
     · letI:= (E.tag j).M; exact integrable_zero ..
     rw [plaidF_constSky,map_zero,show e 0=0 from map_zero _,dot_zero]; simp
   | cons a l IH=>
     obtain ⟨hk',Hk⟩:=IH (fun i hi=> hS _ (List.mem_cons_of_mem a hi))
     obtain ⟨hl',hL⟩:= wordAnswerSky E P hP hx t Hv he he' hr H hs hu hp a.2 (hS a (List.mem_cons_self ..))
     let q:=(a.1:ℂ); let W:=tracesFtSky E P a.2; let V:= fun (j:Fin E.count) z=> q*W j z; let Q:=traySky E l P; let Λ:=sculptFtSky (hk:=hk) (h:=h) (c:=c) (T:=T) (R:=R) (U:=U) P a.2
     have ht : ∀ j, letI:= (E.tag j).M; Integrable (V j) (E.tag j).μ:= fun j => by letI:= (E.tag j).M; exact (hl' j).const_mul q
     refine ⟨fun j=>?_,?_⟩
     · letI:= (E.tag j).M; exact (ht j).add (hk' j)
     change ‖plaidFtSky E (fun j z=> V j z+ Q j z)-A (a::l)‖ ≤ ‖q‖*glare B ε r D a.2.length+ _
     rw [plaidF_addSky E V Q ht hk', show plaidFtSky E V=_ from plankSky E _ W,show A (a::l)= q*Λ+A l from ?_,add_sub_add_comm,← mul_sub]
     · apply (norm_add_le ..).trans; rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_left hL (norm_nonneg _)) Hk
     let Y:= (a.2.map P).prod; let X':= honors l P
     change dot K (e ((R i).read (MvPolynomial.C q * Y + X'))) = q*Λ+ _
     rw [_root_.map_add,C_mul',_root_.map_smul]; change dot K (aeval _ _) = _; simp only [_root_.map_add, _root_.map_smul,smul_eq_mul]; exact send1 K a.1 _ _
end YM.Next.Rank.Tapes.West
