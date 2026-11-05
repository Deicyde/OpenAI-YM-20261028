import YM.MergeProof.West.Canvas
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition
variable {G:Gauge}{N n p k q i d D:ℕ} {C:Family G} {R:Lead G C.S p}
   {b:ℝ} {c:Course C N p k}{x:Points n}{hk:i<k}{h:middle C.path.levels b k ≤ i}
   {T τ U ε g B Y L} (E:StageNow (d:=d) c R x b hk h q T τ U ε)

lemma plank (s : ℂ) (X' : (j : Fin E.count) → (E.tag j).Θ →ℂ) : plaidFt E (fun j z=>s * X' j z)=s*plaidFt E X':= by
    unfold plaidFt mixedFt; rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro i _; letI:= (E.tag i).M; dsimp only; rw [integral_const_mul,mul_left_comm]
lemma send1 (K:Prop)(a:ℝ)(b c:ℂ):dot K ((a:ℂ)*b+c)=(a:ℂ)*dot K b+dot K c:=by unfold dot; split<;>simp
variable (S:List (ℝ × List (modes (Fin n))))
variable (P:modes (Fin n) → poly (Chamber G C.S (i+1) p))
def tray := fun (j:Fin E.count) z=> honors S (p_lanter E (offerNow E P) j z).part
def platter := dot ((Ship.yard C b c.allow p).hand T.1) (e_legance b c x hk h T U ((R i).read (honors S P)))
def grantS (B ε r:ℝ) (D:ℕ) := (S.map fun w=> ‖((↑w.1):ℂ)‖ * glare B ε r D w.2.length).sum
lemma grantS_nn (B ε r:ℝ) (D:ℕ)(h:1≤ B)(hp:0≤ε)(hv:0≤r):0≤grantS S B ε r D:=by
   induction S with
   | nil=>rfl
   | cons i l ih=>exact add_nonneg (mul_nonneg (norm_nonneg _) (glare_nn _ _ _ _ _ h hp hv)) ih
variable (hP : ∀ u,P u ≠ 0 → ∃ i : ViewFt C k b p d x hk,i.val.val=u)
variable (hx:roomTest C.path.levels b k p d q) (t:Metal b c R hk ε τ g B Y L) (Hv:Healthy g (d_olm x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U) (he: 0 < ε)(he':ε≤1)
   {r:ℝ} (hr:0≤r)
variable (H:∀ i, Poetic (P i)) (hs:∀ i,totalDegree (P i)≤ D) (hu:∀ i,coin (P i)≤ r) (hp:∀ u : Manner n,∀ i'∈(P u.val).vars,spotFt b (i+1) d (show i+1≤k from hk) x u i' (C:=C))
include hP hx t Hv he he' hr H hs hu hp
lemma sweep (hS: ∀ t∈S,∀ i∈t.2,i.val ⊆ T.2.val.val.val) :
   (∀ j,letI:= (E.tag j).M; Integrable (tray E S P j) (E.tag j).μ) ∧
    ‖plaidFt E (tray E S P)-platter (c:=c) (R:=R) (hk:=hk) (h:=h) (T:=T) (U:=U) S P‖ ≤ grantS S B ε r D:= by
   let A:= fun x=> platter (c:=c) (R:=R) (hk:=hk) (h:=h) (T:=T) (U:=U) x P
   let K:= (Ship.yard C b c.allow p).hand T.1; let e:= e_legance b c x hk h T U
   induction S with
   | nil=>
     change _ ∧ ‖plaidFt E (fun _ _=>0)-dot K (e ((R i).read 0))‖≤ 0
     refine ⟨fun j=>?_,?_⟩
     · letI:= (E.tag j).M; exact integrable_zero ..
     rw [plaidF_const,map_zero,show e 0=0 from map_zero _,dot_zero]; simp
   | cons a l IH=>
     obtain ⟨hk',Hk⟩:=IH (fun i hi=> hS _ (List.mem_cons_of_mem a hi))
     obtain ⟨hl',hL⟩:= wordAnswer E P hP hx t Hv he he' hr H hs hu hp a.2 (hS a (List.mem_cons_self ..))
     let q:=(a.1:ℂ); let W:=tracesFt E P a.2; let V:= fun (j:Fin E.count) z=> q*W j z; let Q:=tray E l P; let Λ:=sculptFt (hk:=hk) (h:=h) (c:=c) (T:=T) (R:=R) (U:=U) P a.2
     have ht : ∀ j, letI:= (E.tag j).M; Integrable (V j) (E.tag j).μ:= fun j => by letI:= (E.tag j).M; exact (hl' j).const_mul q
     refine ⟨fun j=>?_,?_⟩
     · letI:= (E.tag j).M; exact (ht j).add (hk' j)
     change ‖plaidFt E (fun j z=> V j z+ Q j z)-A (a::l)‖ ≤ ‖q‖*glare B ε r D a.2.length+ _
     rw [plaidF_add E V Q ht hk', show plaidFt E V=_ from plank E _ W,show A (a::l)= q*Λ+A l from ?_,add_sub_add_comm,← mul_sub]
     · apply (norm_add_le ..).trans; rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_left hL (norm_nonneg _)) Hk
     let Y:= (a.2.map P).prod; let X':= honors l P
     change dot K (e ((R i).read (MvPolynomial.C q * Y + X'))) = q*Λ+ _
     rw [_root_.map_add,C_mul',_root_.map_smul]; change dot K (aeval _ _) = _; simp only [_root_.map_add, _root_.map_smul,smul_eq_mul]; exact send1 K a.1 _ _
end YM.Next.Rank.Tapes.West
