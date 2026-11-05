import YM.Extension.UV.Station.Stencil
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Set Function Filter Lattice RG Laurent Bloch Metric Matrix Wilson Exterior Precision Next.Free
open scoped Topology BigOperators Classical
variable {G:Gauge} {A:Levels G}

lemma constant_ball {j t:ℕ} {c f:Side} (P:Flight j t) (K:KernelChoices) (hf:f.val=c.val*P.L.val) (ht:4≤t) (u v:Site f) (i b:TypeFace 2) (x:Co c (TypeFace 2)→ℝ) (hx:x=fun e=>if e.2=b then 1 else 0):
    let W := installed (P.visitRatio hf) (P.duo K.penalty).T
    (W*ᵥ x) (u,i)= (W*ᵥ x) (v,i) := by
  intro W
  have hj:=P.legal; obtain ⟨-,h⟩:= secure_both K.penalty K.penalty_pos hj ht
  have H : approached W* rotations c (TypeFace 2)= readings (P.visitRatio hf) (TypeFace 2)*solo c (P.fromBank (Flight.wire K.penalty) 2):= P.sail_run (c:=c) hf h hj 2 -- check order
  let h' (i b:TypeFace 2) (l:Site P.L) := if l=0 then toll P.L 2*(if i=b then (1:ℂ) else 0) else 0
  have hw i b (l:Site P.L) : (P.fromBank (Flight.wire K.penalty) 2 0) (l,i) b=h' i b l:=by
     dsimp [Flight.fromBank,downAlias, h']; split
     · subst l; simp [P.wire_origin,Matrix.one_apply]
     rename_i hn
     simp [P.wire_none K.penalty hn]
  have e u : ((W *ᵥ x) (u,i):ℂ)=h' i b 0 := by
     have he := congr_fun (congr_fun H (u,i)) (0,b)
     simp only [Matrix.mul_apply,Fintype.sum_prod_type] at he
     simp only [rotations,cell,mon_zero,mode_constant,approached,Matrix.map_apply,Matrix.of_apply,solo,fiber,mul_ite,mul_zero,mul_one,Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_ite_irrel,Finset.sum_const_zero] at he -- may norm casts
     calc
       _ = ∑ y : Site c, ↑(W (u,i) (y,b)) := by push_cast; simp [Matrix.mulVec, dotProduct,Fintype.sum_prod_type,hx]
       _ = ∑ k, if i=k then ∑ l: Site P.L, mode (aliasAt (mon (0:Site c)) l) (lift u)* h' k b l else 0 := by
         rw [he,Finset.sum_comm]
         refine Finset.sum_congr rfl fun a ha=>?_;
         simp_rw [sample,ite_mul,zero_mul,mon_zero,hw]
         split_ifs <;> simp [*]
       _ = _ := by simp [h', Finset.sum_ite_eq', mul_ite,aliasAt]
  exact Complex.ofReal_injective ((e u).trans (e v).symm)

lemma kneel {α:Type*} {f:Side} [DecidableEq α] [Fintype α] (s:Axis) (x:Co f α→ℝ) (u):
    ((motion α f [s]) *ᵥ x) u = x (u.1+step s,u.2)-x u:= by rw [motion_walk,motion_zero,Matrix.mul_one]; exact knock_entry _ _ s _ x

lemma cancellation_eq (X:Horizon A)
    (hp : ∀ n m:ℕ,m<n → (X.towers n m).T=((destination A n m).duo A.clock.kernel.penalty).T) (P:MapPrices) (hM : X.Suffices P) m p n (hn:m<n) (a:Axis) :
    let S:=A.clock.op m p
    let V:=advanceC S.patch.L (X.towers n m).T [a]
    let _c:=A.S.side m p
    ∀ e : TypeFace 2, (installed S.ratio V *ᵥ fun q=> if q.2=e then 1 else 0)=0 := by
  intro S V c i
  let f:=A.S.side (m+1) p
  let j := A.clock.J (m+1)
  have h0 : 4≤ j := A.clock.adm _
  have hd:=hM.costs n m hn
  have hR:=hM.crossings n m p hn
  let Q:=(destination A n m)
  let W:=(X.towers n m).T
  have hx: W=(Q.duo A.clock.kernel.penalty).T:= hp n m hn
  have hv : f.val=c.val*Q.L.val:= S.sizes
  let Z := installed S.ratio W
  let x : Co c (TypeFace 2) → ℝ := fun q=> if q.2=i then 1 else 0
  have hS (u v : Site f) (k:TypeFace 2) : (Z*ᵥ x) (u,k)=(Z*ᵥ x) (v,k) := by unfold Z; rw [hx]; exact constant_ball Q _ hv (A.clock.adm _) u v k i x rfl
  change installed S.ratio (advanceC S.ratio.count W [a]) *ᵥ x=0
  rw [flow_movement S.ratio W [a] (A.S.block_odd _) ?_,← mulVec_mulVec]
  · ext y; convert sub_eq_zero.mpr (hS (y.1+step a) y.1 y.2) using 1; · exact kneel _ _ _
    rfl
  intro u hu; dsimp only [j] at h0; simp only [List.length_singleton] at hu
  exact ⟨_,_,P.alpha_pos j,(hd.2.2.2 u (show _≤_ by omega)).2⟩

lemma cancellation (X:Horizon A) {l} (hp : Next.Free.Present A X l) (P:MapPrices) (hM : X.Suffices P) m p n (hn:m<n) (a:Axis) :
    let S:=A.clock.op m p
    let V:=advanceC S.patch.L (X.towers n m).T [a]
    let _c:=A.S.side m p
    ∀ e : TypeFace 2, (installed S.ratio V *ᵥ fun q=> if q.2=e then 1 else 0)=0 :=
 cancellation_eq X (fun n m hn=> (hp.2 n m hn).2) P hM m p n hn a
end YM.Extension.UV.Linear
