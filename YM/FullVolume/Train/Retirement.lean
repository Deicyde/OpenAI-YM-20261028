import YM.FullVolume.Train.Mast
/-! Calculus ext-T losses.Free. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Retort
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid Train Flight
open scoped Topology BigOperators ComplexConjugate
variable {X Y Z:Type}
def Parade (S:ℕ→Row X Y):= Stock (α:=fun _=>X) (β:=fun _=>Y) (fun _=>1) S ∧ ∃ T,Tendsto S atTop (𝓝 T)
variable [Fintype X][Fintype Y][Fintype Z]
variable {S S':ℕ→Row X Y} {T:ℕ→Row Y Z}
lemma stock_take {S:ℕ→Row X Y} (h:Parade S): ∃ R σ C,Fleet S R σ C:=by
    obtain ⟨σ,C,hp,hC,H⟩:= h.1.uniform
    obtain ⟨R,hR⟩:= h.2
    exact ⟨R,σ,C*1,hR,hp,Eventually.of_forall H⟩
lemma assembly {S:ℕ→Row X Y}(h:Stock (α:=fun _=>X) (β:=fun _=>Y) (fun _=>1) S)(x:Axis) (he:∀ p∈baseCube,q p x≠0→∃ t,Tendsto (fun i=> (S i).read p) atTop (𝓝 t)): Parade S:=by
    refine ⟨h,?_⟩
    obtain ⟨σ,C,hp,_,H⟩:= h.uniform
    obtain ⟨F,hF⟩ :∃ F,Fleet S F σ (C*1):=by
       apply amalgam hp (Eventually.of_forall H); intro r t F Q hr ht hu hy
       apply bank_injective (Row.rights _ _ hu.lives hp.le) (Row.rights _ _ hy.lives hp.le); apply acts_of_cube (Row.rights _ _ hu.lives hp.le) (Row.rights _ _ hy.lives hp.le)
       refine renew_q F.read Q.read x (fun p hp'=>read_here _ ⟨σ,_,hp,hu.lives⟩ hp') (fun p hp'=>read_here _ ⟨σ,_,hp,hy.lives⟩ hp') fun p hk hb=>?_
       obtain ⟨R,he⟩:=he p hk hb; exact (tendsto_nhds_unique (hu.reads hk.1) (he.comp hr.tendsto_atTop)).trans (tendsto_nhds_unique (he.comp ht.tendsto_atTop) (hy.reads hk.1))
    exact ⟨F,hF.hull⟩
lemma villages {S:ℕ→Row X Y}(hs:Stock (α:=fun _=>X) (β:=fun _=>Y) (fun _=>1) S)(he:∀ n:Side,∃ A,Tendsto (fun i=> (S i).acts n) atTop (𝓝 A)): Parade S:=by
   obtain ⟨σ,C,hp,hC,H⟩:=hs.uniform
   obtain ⟨F,hF⟩:=amalgam hp (Eventually.of_forall H) fun r t F Q hr ht hu hy=> bank_injective (Row.rights _ _ hu.lives hp.le) (Row.rights _ _ hy.lives hp.le) (fun n=> (tendsto_nhds_unique (hu.muster n) ((he n).choose_spec.comp hr.tendsto_atTop)).trans (tendsto_nhds_unique ((he n).choose_spec.comp ht.tendsto_atTop) (hy.muster n)))
   exact ⟨hs,F,hF.hull⟩
lemma Parade.opp (h: Parade S): Parade fun i=> transRows (S i):=by
   obtain ⟨g,hf⟩:= h.2
   exact ⟨h.1.flipped, transRows g,tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>tendsto_pi_nhds.mpr fun x=>tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf j) i) (-x)⟩
lemma Parade.demise (h: Parade S)(g: Parade S'): Parade fun i=> minusRows (S i) (S' i) := ⟨ h.1.minus g.1,_,h.2.choose_spec.sub g.2.choose_spec⟩
lemma Parade.refs (h: Parade S)(g: Parade S'): Parade fun i=> plusRows (S i) (S' i) := by
    have he : ∀ R T:Row X Y,plusRows R T= R+T :=by intro R T; funext i j k; unfold plusRows minusRows scaleRows; simp
    refine ⟨Stock.plus h.1 g.1,_,(h.2.choose_spec.add g.2.choose_spec).congr fun i=>(he ..).symm⟩
lemma Parade.boost (h: Parade S)(r:ℝ): Parade fun i=> scaleRows r (S i):=⟨h.1.weight r,_,h.2.choose_spec.const_smul r⟩
lemma launch (A:Row X Y)(h:Whole A) : Parade fun _=> A :=⟨Stock.constant A h,_,tendsto_const_nhds⟩
lemma Parade.prod (h:Parade S) (g:Parade T): Parade (fun i=> composeRows (S i) (T i)):=by
    obtain ⟨R,w,q,H⟩:= stock_take h; obtain ⟨Z',u,v,G⟩:=stock_take g
    refine assembly ?_ 0 fun p hp _=> ⟨_,((H.reads hp.1).matrix_mul (G.reads hp.1)).congr (fun i=> ((h.1.whole i).read (g.1.whole i) hp.1).symm)⟩
    simpa only [one_mul] using h.1.times g.1
lemma Parade.dash (h: Parade S)(x:Axis): Parade fun i=> dashAxis x (S i):=by
    obtain ⟨R,w,c,H⟩:= stock_take h
    refine assembly (dash_stock h.1 x) x fun p hp hb=>⟨_,(((H.reads hp.1).sub (H.reads (real_blank hp.1 x))).const_smul (q p x)⁻¹).congr fun i=>?_⟩
    change _⁻¹ • ((S i).read p - _)=_
    rw [← read_part (h.1.whole i) x hp.1,inv_smul_smul₀ hb]
lemma Parade.sheds {j}{S:ℕ→Row X (TypeFace (j+1))}(h: Parade S)(x:Axis): Parade fun i=> shed x j (S i):=by
    obtain ⟨R,w,c,H⟩:= stock_take h
    refine assembly (shed_stock h.1 x) x fun p hp hb=>?_
    exact ⟨_,((H.reads (real_blank hp.1 x)).matrix_mul tendsto_const_nhds).congr fun i=> (read_shed (h.1.whole i) x hp.1).symm⟩
lemma Parade.bequest {j}{S:ℕ→Row X (TypeFace (j+1))}(h: Parade S)(l: List Axis): Parade fun i=> folded j (S i) l :=by
    induction l generalizing S with
    | nil=> exact launch (0:Row X _) barren_whole
    | cons s l ih=> exact Parade.refs ((h.dash s).prod (launch _ (constant_whole _))) (ih (h.sheds s))
lemma Parade.cap {j}{S:ℕ→Row X (TypeFace (j+1))}(h: Parade S): Parade fun i=> capLift j (S i):=h.bequest _
lemma Parade.note {j}{S:ℕ→Row (TypeFace (j+1)) X}(h: Parade S): Parade fun i=> supplyLift j (S i):= h.opp.cap.opp
lemma Parade.priors {S:ℕ→Row (TypeFace 2) (TypeFace 2)}(h:Parade S): Parade fun i=> Double.both (S i):=by
   have hp:Parade fun i=>Double.X (S i):= ((h.note.prod (launch _ (Whole.boundary 1))).note (j:=2)).cap
   exact Parade.cap (h.note.demise ((launch _ (Whole.boundary 3)).opp.prod hp))
end YM.Next.Free.Retort
