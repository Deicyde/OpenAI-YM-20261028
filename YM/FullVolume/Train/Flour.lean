import YM.FullVolume.Train.Retirement
/-! Canonical Frontier W fixed algebra, real #site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Retort
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid Train Flight
open scoped Topology BigOperators ComplexConjugate
lemma _root_.Filter.Tendsto.matrix_product {α β γ : Type*}[Fintype β]{R:ℕ→Matrix α β ℝ}{S:ℕ→Matrix β γ ℝ} {r s}(h:Tendsto R atTop (𝓝 r))(hx:Tendsto S atTop (𝓝 s)): Tendsto (fun i=> R i*S i) atTop (𝓝 (r*s)):= tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> tendsto_finsetSum _ fun x _=> ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) x).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hx x) j))
lemma promote_crew {X Y:Type}{c f:Side} (r:Ratio c f){S:ℕ→Cross r.count X Y}{R σ C}(h:Fleet S R σ C): Tendsto (fun i=>installed r (S i)) atTop (𝓝 (installed r R)):=tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=> tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (h.muster c) (splitCo r X i)) j
lemma copies_crew {X Y:Type}{c f:Side} (r:Ratio c f){S:ℕ→Cross r.count X Y}{U}(h:Tendsto (fun i=>installed r (S i)) atTop (𝓝 U)): Tendsto (fun i=> (S i).acts c) atTop (𝓝 (U.submatrix (splitCo r X).symm id)) :=by
  apply tendsto_pi_nhds.mpr; intro i; refine tendsto_pi_nhds.mpr fun j=>?_
  have H:= (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h ((splitCo r X).symm i)) j)
  unfold installed at H; simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply,id_eq] using H
lemma return_crew {ι:Type}[Fintype ι][DecidableEq ι] {A:ℕ→Row ι ι} (ha:Warm (m:=ι) A)(hp:Parade A): Parade fun i=> oppositeRow (A i):= by
     obtain ⟨hv,H⟩:= heated ha; obtain ⟨S,T,h,hD,ht⟩:= hv.stock.uniform; refine ⟨hv.stock,?_⟩
     obtain ⟨R,u,v,hV⟩:= stock_take hp
     obtain ⟨F,hF⟩:=amalgam h (Eventually.of_forall ht) fun r q F Q hr hq hS hM=>bank_injective (Row.rights _ _ hS.lives h.le) (Row.rights _ _ hM.lives h.le) (fun n=> by
           have he : F.acts n*R.acts n=1:= tendsto_nhds_unique (((hS.muster n).mul ((hV.muster n).comp hr.tendsto_atTop)).congr (fun i=>(H _).2 n)) (tendsto_const_nhds (x:=(1:Matrix _ _ _))) -- unders
           have hu : Q.acts n*R.acts n=1:= tendsto_nhds_unique (((hM.muster n).mul ((hV.muster n).comp hq.tendsto_atTop)).congr (fun i=>(H _).2 n)) tendsto_const_nhds
           calc
            _ = F.acts n*(R.acts n*Q.acts n):= by rw [mul_eq_one_comm.mp hu,mul_one]
            _ = _:= by rw [←mul_assoc,he,one_mul])
     · exact ⟨F,hF.hull⟩
variable {G:Gauge} (A: Levels G)(m:ℕ)
local notation "L"=> A.S.block m
private lemma pols {k:ℝ}(h:0<k) {j}(hj:4 ≤ j){v:ℕ→Train j}(he:∀ p∈baseCube, ∃ M F,Tendsto (fun n=> (pink k (v n)).read p) atTop (𝓝 F) ∧ Tendsto (fun n=> (blue k (v n)).read p) atTop (𝓝 M)): Parade (fun i=> blue k (v i)) ∧ Parade (fun i=> pink k (v i)):=by
    obtain ⟨ha,hb⟩:= heart_saves _ h hj v
    choose M F hF hM using he; exact ⟨assembly hb 0 fun p hp _=> ⟨M p hp,hM p hp⟩,assembly ha 0 fun p hp _=>⟨F p hp,hF p hp⟩⟩
local notation "k" => A.clock.kernel.penalty
private lemma runout: Parade (fun i=> blue k (location A i m)) ∧ Parade fun i=> pink k (location A i m):= pols A.clock.kernel.penalty_pos (A.clock.adm m) fun _ hp=>OnTrack.blade A m hp A.clock.kernel.penalty_pos
lemma dominant (l:ℝ)(hl:0≤l): Parade (fun i=> pink k (location A i m)) ∧ Parade (fun i=> blue k (location A i m)) ∧ Parade (fun i=> pledge k l (location A i m)) ∧ Parade fun i=> amend k l (location A i m):=by
    obtain ⟨ha,hb⟩:= runout A m
    let T := fun i=>location A i m; have hX : Parade fun i=> drawer k (T i):=(launch _ (Whole.boundary 2)).prod ha
    have hQ : Parade fun i=> pledge k l (T i):= Parade.refs ha ((hX.opp.prod hX).boost l)
    exact ⟨hb,ha,hQ,return_crew (pledge_warm k l A.clock.kernel.penalty_pos hl (A.clock.adm m) T) hQ⟩
private lemma moving {p:Momentum}(hk:q p 0 ≠ 0): p≠0:=fun h => hk (by rw [switch_axis,h]; simp)
lemma concord : Parade (X:=Co L (TypeFace 1)) (Y:=TypeFace 1) (fun i=> (duo k (destination A i m)).A0) ∧ Parade (X:=Co L (TypeFace 2)) (Y:=TypeFace 2) fun i=> (duo k (destination A i m)).T:=by
    let P n:= destination A n m
    obtain ⟨h1,h2⟩:= secure_both k A.clock.kernel.penalty_pos (A.clock.adm (m+1)) (A.clock.adm m); obtain ⟨σ,C,hσ,hC,H⟩:= h1.bankCost (A.clock.adm _) 1 (u:=[]) (by simp)
    obtain ⟨t,U,ht,hU,T⟩:= h2.bankCost (A.clock.adm _) 2 (u:=[]) (by simp)
    have hv: Stock (α:=fun _=>_) (β:=fun _=> TypeFace 1) (fun _ :ℕ=>1) fun n=>(duo k (P n)|>.A0 :Cross L (TypeFace 1) _):=by
       refine ⟨fun i=> zero_le_one,σ,C/((L).val:ℝ)^(1+([]:List Axis).length),hσ,by have h:= side_pos L; positivity,fun i=>?_⟩; rw [mul_one]; exact H (P i)
    have hh: Stock (α:=fun _=>_) (β:=fun _=> TypeFace 2) (fun _ :ℕ=>1) fun n=>(duo k (P n)|>.T:Cross L (TypeFace 2) _):=by
       refine ⟨fun i=> zero_le_one,t,U/((L).val:ℝ)^(2+([]:List Axis).length),ht,by have h:= side_pos L; positivity,fun i=>?_⟩; rw [mul_one]; exact T (P i)
    refine ⟨assembly hv 0 fun p hp ht=>?_, assembly hh 0 fun p hp ht=>?_⟩
    · choose H h using (OnTrack.presentT A m p hp (moving ht) A.clock.kernel.penalty_pos).1; exact ⟨Matrix.of H,tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=> h i j⟩
    choose H h using (OnTrack.presentT A m p hp (moving ht) A.clock.kernel.penalty_pos).2; exact ⟨Matrix.of H,tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=> h i j⟩
lemma angular (x y:ℝ)(he:0≤y) : Parade fun i=> rollFunds k x y (destination A i m):= by
    have hk :0<k := A.clock.kernel.penalty_pos; have hM:= A.clock.adm (m+1); have ht:=A.clock.adm m; let P i:=destination A i m
    obtain ⟨-,-,hp,_⟩:= dominant A m y he
    have hb : Parade fun n=> blue k (P n|>.wing):=(dominant A (m+1) 0 le_rfl).2.1
    obtain ⟨hc,hd⟩ : Parade (fun n=> blue k (P n|>.land)) ∧ Parade fun n=> pink k (P n|>.land) := pols hk ht fun p hp' => by
       obtain ⟨v,u,hv,hu⟩:= OnTrack.blade A m hp' hk
       have he : ∀ᶠ i:ℕ in atTop,(P i).land=location A i m:= (eventually_gt_atTop _).mono fun n h=> (loc_land A _ _ h).symm
       exact ⟨v,u,hv.congr' (he.mono fun i h=>congr_arg (fun z=> Row.read (pink k z) p) h.symm), hu.congr' (he.mono fun i h=>congr_arg (fun z=>Row.read (blue k z) p) h.symm)⟩
    have hD: Parade fun n=> treble k y (P n|>.land):= return_crew (bail_warm k y hk he ht (fun n=> P n|>.land)) (Parade.refs (launch _ (Whole.coin (TypeFace 3))) ((((launch _ (Whole.boundary 2)).prod hc).prod ((launch _ (Whole.boundary 2)).opp)).boost y))
    have hT := (concord A m).2
    obtain ⟨B,b,c,hB⟩:=stock_take hb; obtain ⟨R,t,G',hR⟩:=stock_take hT
    have hv : Parade (X:=Co (L) (TypeFace 2)) (Y:=TypeFace 2) (fun i=> buckle k (P i)):=by
        obtain ⟨σ,C,hσ,hC,H⟩:= (budgets_linear k hk hM ht).1.uniform
        let g:= fee (j:=A.clock.J (m+1)) 2 (P 0)
        have hg: 0<g:=by unfold g fee; positivity
        refine villages ⟨fun i=> zero_le_one,σ,C*g,hσ,mul_pos hC hg,fun i=> ?_⟩ fun n=>?_
        · rw [mul_one]; exact H (P i)
        let f:= n*(L); let F:= (P 0).visitRatio (c:=n) (f:=f) rfl
        have hu:= (hB.muster f).matrix_product (promote_crew (S:=fun i=> (P i|>.duo k).T) F hR)
        exact ⟨_,copies_crew F (hu.congr fun i=> (buckle_physical k hk ht (P i) (c:=n) (f:=f) rfl).symm)⟩
    let Z:= (launch _ (Whole.boundary 1))
    have hI : Parade fun n=> gap k (P n):= Parade.demise (hc.demise (hT.opp.prod hv)) ((Z.prod Z.opp).boost k⁻¹)
    have hL : Parade fun n=> leftFunds k (P n):=((hd.prod hI).prod hd).priors
    have hS:Parade (X:=Co (L) (TypeFace 3)) (Y:=TypeFace 2) (fun i=> charge k (P i)):=by
        obtain ⟨σ,C,hσ,hC,H⟩:= (budget_charge k hk hM ht).uniform
        let g:= fee (j:=A.clock.J (m+1)) 3 (P 0)
        have hg: 0<g:=by unfold g fee; positivity
        obtain ⟨W,B',C',hW⟩:=stock_take hd
        refine villages ⟨fun i=> zero_le_one,σ,C*g,hσ,mul_pos hC hg,fun i=>?_⟩ fun n=>?_
        · rw [mul_one]; exact H (P i)
        let f:= n*L; let F:= (P 0).visitRatio (c:=n) (f:=f) rfl
        have hu:= (((tendsto_const_nhds (x:=d 2 f)).matrix_product (hB.muster f)).matrix_product (promote_crew (S:=fun i=> (P i|>.duo k).T) F hR)).matrix_product (hW.muster n)
        exact ⟨_,copies_crew F (hu.congr fun i=> (mark_charge k hk ht (P i) (c:=n) (f:=f) rfl).symm)⟩
    have hf: Parade fun n=> render k x y (P n):= Parade.demise (((hL.refs hL.opp).boost (1/2)).refs ((launch _ (Whole.coin (TypeFace 3))).boost y)) ((hS.cap.opp.prod hS.cap).boost x)
    exact (hD.opp.prod hf).prod hD
end YM.Next.Free.Retort
