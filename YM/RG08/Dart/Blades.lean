import YM.RG08.Dart.Cones
/-! # Pointed lift strip estimate with independent-leg gain. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter
open UVExt.Paths Push.AbsoluteSums Quire Vale Matrix
open scoped Topology BigOperators ContDiff Classical
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{W:Type}{r i k:ℕ}{σ v C B:ℝ}{G:Gauge}

abbrev moteP (W:Type):= Cover× W
abbrev Leaf (G:Gauge):= moteP (Loc G 1)
abbrev Blade (G:Gauge):= moteP (Loc G 2)
private def make (x: Cover)(i:Axis): List Fleck:= (budge_spike x i).choose
private lemma make_ok (x:Cover)(i:Axis): ∀ v∈make x i, ‖v.1‖ ≤ 1 ∧ size v.2.1 ≤ size x:= (budge_spike x i).choose_spec.2.1
private lemma make_length (x:Cover)(i:Axis): (make x i).length ≤ size x := (budge_spike x i).choose_spec.1
-- signed coefficient at every face with own tag
abbrev wool {W:Type} (w:ℝ)(x:moteP W) := Real.exp (w*size x.1)
private def cutP (L: List Fleck)(s:G.ColorIndex)(i:Blade G) := (L.map fun f=> if i=(f.2.1, plaquette f.2.2,s) then f.1 else 0).sum
def vein (G:Gauge) : Vale.Paper (Loc G 1) (Loc G 2):= fun p=> cutP (make p.1 (axisEquiv.symm p.2.1)) p.2.2
private lemma cut_price (h:0≤v)(P:List Fleck)(he: ∀ i∈P,‖i.1‖≤1 ∧ size i.2.1 ≤ k)(s:G.ColorIndex): Charge (wool v) (cutP P s) (P.length*Real.exp (v*k)):= by
   induction P with
   | nil=> simp only [List.length_nil,Nat.cast_zero,zero_mul]; exact Charge.zero _
   | cons i p ih=>
      have hp := he i (List.mem_cons_self); rw [List.length_cons,Nat.cast_add,add_mul, Nat.cast_one,one_mul,add_comm]; let t:Blade G:=(i.2.1,plaquette i.2.2,s); let A(z:Blade G):=if z=t then i.1 else 0
      have hf:Charge (wool v) A (Real.exp (v*k)) := by
         unfold Charge; refine ⟨fun i=> mul_nonneg (Real.exp_pos _|>.le) (norm_nonneg _), summable_of_ne_finset_zero (s:={t}) (fun i hi=>by simp [A, mt mem_singleton.mpr hi]),?_⟩
         rw [tsum_eq_single t,show A t=i.1 from if_pos rfl]; refine (mul_le_of_le_one_right (Real.exp_pos _|>.le) hp.1).trans (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hp.2) h)); intro i hi; simp [A,hi]
      rw [show cutP (i::p) s= A+cutP p s from rfl]; exact Charge.add hf (ih fun j hj=>he j (List.mem_cons_of_mem _ hj)) (fun i=> Real.exp_pos _|>.le)
private lemma cutp_values (L:List Fleck)(s:G.ColorIndex)(F: Blade G→ℝ): HasSum (fun i=>cutP L s i*F i) (L.map fun i=> i.1*F (i.2.1,plaquette i.2.2,s)).sum:= by
   induction L with
   | nil=> simp [cutP]
   | cons i l ih=>
      let t: Blade G:=(i.2.1,plaquette i.2.2,s); let q v:= (if v=t then i.1 else 0)*F v; let u:=i.1*F t
      have hk : HasSum q u:= by rw [show u=q t from (by simp [q,u])]; exact hasSum_single _ (fun i hi=>by simp [q,hi]) -- name
      refine (hk.add ih).congr_fun fun x=>?_; exact add_mul .. -- congr orientation
abbrev gapPrice (v:ℝ) := v⁻¹
lemma vein_price (w:Leaf G)(hv:0<v): Charge (wool v) (vein G w) (gapPrice v * wool (2*v) w) := by
    let i:=axisEquiv.symm w.2.1
    let A:=make w.1 i; have hf:= cut_price hv.le A (make_ok w.1 i) w.2.2; unfold vein
    let x:ℝ:=v*size w.1
    apply Ink.raise hf; calc
       _ ≤ (size w.1:ℝ)*Real.exp x:= mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (make_length ..)) (Real.exp_pos _|>.le)
       _ ≤ v⁻¹ *Real.exp x*Real.exp x:= by gcongr; apply (le_inv_mul_iff₀ hv).mpr; exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
       _=gapPrice v*wool (2*v) w:= by unfold gapPrice wool; rw [mul_assoc,← Real.exp_add]; congr 2; unfold x; ring
-- color factors appear only on matching indices, giving direct covariant tensor role
lemma vein_o (a:Leaf G)(x:Blade G)(h:x.2.2≠a.2.2): vein G a x=0:=by
   unfold vein cutP
   generalize hL:make _ _=l
   clear hL
   induction l with
   | nil=> rfl
   | cons b l ih=>simp only [List.map_cons,List.sum_cons,ih,add_zero]; exact if_neg fun H=>h (congr_arg (fun z: Blade G=>z.2.2) H)
lemma vein_self (x y:Cover)(a b)(s t:G.ColorIndex): vein G (x,a,s) (y,b,s)=vein G (x,a,t) (y,b,t):=by
   simp [vein,cutP]

-- deterministic layout memo. no raw op continuity beyond weights.
def dart (U:Rooted E (Loc G 1) r): Rooted E (Loc G 2) r := revolve U fun _=> vein G
private lemma pay_ling (W:Type)(r:ℕ)(v:ℝ) : ling (α:=W) (r:=r) v= brocade (wool v) := funext fun i=> bro_lit ..
lemma thorn {U:Rooted E (Loc G 1) r}(h: Quire.Lit U (2*v) C)(hv: 0<v): Quire.Lit (dart U) v (gapPrice v ^r*C):= by
   have hx:= revolves (P:=fun _=>vein G) (V:=U) (show Quire.Ink (brocade (wool (2*v))) U C by rw [← pay_ling]; exact h) (show 0 ≤ (fun _ : Fin r=>gapPrice v) from fun i=>inv_nonneg.mpr hv.le) (fun _ x=>vein_price x hv) (fun i=> Real.one_le_exp (mul_nonneg hv.le (Nat.cast_nonneg _))) -- V name
   simpa only [Quire.Lit, dart,pay_ling,prod_const,card_univ,Fintype.card_fin] using hx
lemma thorn_p {U:Rooted E (Loc G 1) r}(h: Quire.Lit U (2*v) C)(hv:0<v): Pens (sires U (bulb (fun _:Fin r=> vein G))) := by
   have hx:= bulb_price (P:=fun _=>vein G) (show Quire.Ink (brocade (wool (2*v))) U C by rw [← pay_ling]; exact h) (show 0 ≤ (fun _ : Fin r=>gapPrice v) from fun i=>inv_nonneg.mpr hv.le) fun _ x=> vein_price x hv
   exact Ink.pens hx (fun i=> fineBro (r:=r) (by intro z; exact Real.one_le_exp (mul_nonneg hv.le (Nat.cast_nonneg _))) i.2)
lemma spine_s {U:Rooted E (Loc G 1) r} (h: Quire.Lit U (2*v) C)(hv:0<v)(hp:Tidy U): Tidy (dart U):= revolve_s _ hp (thorn_p h hv)
-- test law for weights. arbitrary x on cover with site momentum x=v(t). matrix faces periodized all m.
variable {m:Side}
def vline (x:Link G m) (b:Leaf G):= x (wrap m b.1,b.2)
def hline (x:Link G m) (b:Blade G):= Exterior.dColor G m 1 (arm G m 1 x) (wrap m b.1,b.2.1) b.2.2
def vlines (x:Link G m)(k:G.ColorIndex) (b: Edge Cover):= vline x (b.1,coord b.2,k)
lemma hline_b (x:Link G m)(p:Face ℤ)(i:G.ColorIndex): hline x (p.1,plaquette p.2,i)= corner (vlines x i) p := by
    change (d 1 m *ᵥ (parts G 1 (arm G m 1 x) i)) _ = _; rw [d_plaquettes]; unfold corner vlines vline; simp only [map_add,wrap_step]; rfl

def spinD (f: Cover→G.ColorIndex→ℝ)(i:Leaf G):= f (i.1+step (axisEquiv.symm i.2.1)) i.2.2-f i.1 i.2.2
def pathField (x:Link G m) (p:Cover)(i:G.ColorIndex) := budge (vlines x i) p
lemma spoke (x : Link G m) (p:Leaf G) : vline x p - spinD (pathField x) p=pursed (vein G) (hline x) p:= by
    obtain ⟨x',b,j⟩:=p; obtain ⟨b,rfl⟩:=axisEquiv.surjective b
    unfold pursed; unfold vein; rw [show axisEquiv.symm (axisEquiv b)=b from axisEquiv.symm_apply_apply _,(cutp_values (make x' b) j _).tsum_eq] -- normalize coordinates
    simp_rw [hline_b]; unfold spinD pathField
    simp only [show axisEquiv.symm (axisEquiv b)=b from axisEquiv.symm_apply_apply _]
    exact (budge_spike x' b).choose_spec.2.2 (vlines x j)
end YM.RG08.Dart
