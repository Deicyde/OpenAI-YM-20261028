import YM.MultipleContact.Multi.Modify
import YM.MultipleContact.Bunch.Scale
/-! Stage-wise cutoff rows for signed and unsubtracted branches. No center-independent Taylor subtraction hypothesis built into the price. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.MultipleContact.ScheduleRow
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}
set_option quotPrecheck false
local notation "R!" => (fun m:ℕ=> fuga C.path.levels (m+1))
local notation "Y!" => (fun m:ℕ=> Matching.topZone C.path.levels (C.S.block m) (m+1))
lemma shifted {S:Schedule}{f:ℕ → ℝ}{b:ℝ}(h:Note S f b)(hf:S.Gentle)(k:ℕ):Note S (fun i=> f (i+k)) b:=by
      induction k with
      | zero=> simpa using! h
      | succ k ih=> simpa only [Nat.succ_eq_add_one,Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using! ih.scales hf
lemma stride {S:Schedule}(m k:ℕ):(k:ℝ)*S.a (m+k)  <  S.a m:=by
       induction k generalizing m with
       | zero=> simp [S.a_pos]
       | succ k ih=>
         have he:=ih (m+1); have hk: S.a (m+1+k)  ≤  S.a (m+1):= by
                 have hh:= S.embeds_scale (p:=0) (S.toDepth (show m+1  ≤  m+1+k from Nat.le_add_right _ _) 0)
                 exact (le_mul_of_one_le_right (S.a_pos _|>.le) (show (1:ℝ)  ≤  _ by exact_mod_cast (S.toDepth (show m+1 ≤ m+1+k by omega) 0).count.pos)).trans_eq hh
         have hh: (2:ℝ)*S.a (m+1)  ≤  S.a m:=by
                 rw [S.a_step m]; suffices h:(2:ℝ) ≤  (S.block m).val by
                    rw [mul_div_assoc', div_le_iff₀ (lt_of_lt_of_le (by norm_num) h)]; exact mul_le_mul_of_nonneg_left h (S.a_pos _).le |>.trans' (le_of_eq (mul_comm ..))
                 exact_mod_cast (show 2  ≤  _ from (show 2 ≤ 3 by norm_num).trans (S.block_large _))
         push_cast; rw [show m+(k+1)=m+1+k from by omega]; linarith only [he,hk,hh]

def tail (C:Family G)(x:ℝ)(m:ℕ):Prop:=fuga C.path.levels (m+1) ≤ x ∧ x ≤ Matching.topZone C.path.levels (C.S.block m) (m+1)
lemma shell_bound (hw:Note C.S R! (-1)) (hG:G.Simple)(j:ℕ): ∃ ρ> (0:ℝ),∀ x:ℝ,0 < x → x < ρ → ∃ m≥j,tail C x m:=by
     refine ⟨R! j,hw.pos _,fun x hx h=>?_⟩
     obtain hm:∃ n:ℕ,R! (n+j)  ≤  x:= ( ((hw.thins (by norm_num)).comp (tendsto_add_atTop_nat j)).eventually (ge_mem_nhds hx) ).exists
     let n:=Nat.find hm
     have hn:= Nat.find_spec hm
     change R! (n+j)  ≤  x at hn
     have hp: n ≠0:=(fun hq=> (fun ht: (R!) j ≤  x=> (not_le.mpr h ht)) (by simpa only [hq,zero_add] using hn))
     have hl: x  ≤  fuga C.path.levels (n+j):=by
            apply le_of_not_gt
            intro h; apply Nat.find_min hm (show n-1 < n by omega); simpa only [show n-1+j+1=n+j by omega] using h.le
     exact ⟨n+j,Nat.le_add_left ..,hn,hl.trans (Matching.radii C hG _)⟩
def Lag(n:ℕ):ℕ:= 6*(Fintype.card (Signed×Fin n))+2
lemma slots(n m:ℕ): (Fintype.card (Signed×Fin n):ℝ)*(6*C.S.a (m+1+Lag n))  <  C.S.a (m+1):= ((mul_lt_mul_of_pos_right (show (Fintype.card (Signed×Fin n):ℝ)*6 < (Lag n:ℝ) by dsimp [Lag];push_cast;linarith only) (C.S.a_pos _)).trans (stride _ _) |>.trans_le' (by ring_nf; rfl))
lemma point_gap (m:ℕ)(x:ℝ)(hx:tail C x m):4*C.S.a (m+1) < x/16:= by
       have hh:=(C.S.a_pos (m+1)); have hb:(1:ℝ) ≤ (C.path.levels.budget (m+1)).B:=by exact_mod_cast (C.path.levels.budget _).B_pos
       obtain ⟨hL,hR⟩:=hx; unfold fuga at hL
       nlinarith only [mul_le_mul_of_nonneg_right (show (1:ℝ)  ≤  ((C.path.levels.budget (m+1)).B:ℝ)^2 from one_le_pow₀ hb) hh.le, hL, hh]
variable {n:ℕ}[Inhabited (Fin n)]{v:Fin n → C.book.Token}
def mass (v : Fin n  →  C.book.Token):ℕ:= totalDeg (fun i:Fin n=>(v i).1)
def charge (v : Fin n  →  C.book.Token)(h m:ℕ):ℝ:= (R!) m ^ ((mass v:ℝ)-(h:ℝ):ℝ)
structure Portion (C:Family G)(F:Extraction.Order)(h:ℕ)(v:Fin n → C.book.Token)(J:ℕ) (m j:ℕ)(lamp:Lattice.Side)(ε A:ℝ):Prop where
    abort: ∀x'>0,tail C x' m →  ∀ xe,Band n lamp x' xe  →  (∀ k:Fin n×Axis,Placed n (C.S.a j) xe k) → 
      ∃ (x:Fin n → Cover) (u:ℕ×ℕ →  C.book.Ref h)(B:ℝ), xe=C.S.gridPoint j ∘x ∧ (∀ a:Axis, Injective (fun k:Fin n=>xe k a)) ∧
            (∀ᶠ k in F.fuse,‖u k‖  ≤  B) ∧ Drama.Wage F C (Drama.Loss C x v (j:=j) (charge v h m) u) J A
    raw: ∀x'>0,tail C x' m  →  ∃K:Fin n → ℝ, J  ≤  m+1 ∧ 2*C.S.a (m+1)  <  C.S.a J ∧ (∀ k:Fin n,Drama.Wage F C (Drama.Unit C (d:=(v k).1) ((v k).snd)) (m+1+Lag n) (K k)) ∧ ∏ k:Fin n,K k ≤ x'^(-(mass v:ℝ)-ε)
    small: ∀x'>0,tail C x' m  →  ∀ xe,Band n lamp x' xe  →  ∀ s:Fin n,8*‖xe s‖  <  C.S.a J

lemma hold_cost (hc:CellHyp C F)(d:ℕ)(Q:ℝ)(hQ:0 < Q): ∀ᶠ J in atTop,∃A> (0:ℝ),∀w:C.book.Ref d, ‖w‖ < Q → Drama.Wage F C (Drama.Unit C (d:=d) w) J A:=by
      obtain ⟨m,_,a,hA,hw⟩:=hc.centered d 1 Q one_pos hQ; filter_upwards [eventually_ge_atTop m] with J hJ
      refine ⟨a*(C.S.a J)^(-(d:ℝ)-1:ℝ)+1, add_pos_of_nonneg_of_pos (mul_nonneg hA (Real.rpow_pos_of_pos (C.S.a_pos _) _|>.le)) one_pos, fun w hw'=>?_⟩
      have hu:=hw _ hJ 1 one_pos; unfold Drama.Wage; rw [Extraction.Order.fused]; apply hu.mono; intro ip hi; apply hi.mono; intro i' hu; obtain ⟨h,ht⟩:=hu
      -- check fused rewriting
      exact ⟨h, ht w hw'.le 0⟩
lemma micro_budget {ε:ℝ}(hε:0 < ε)(hc:CellHyp C F)(hA:Acme.Aroma C){J:ℕ}:
       ∀ᶠ m in atTop, ∀x'> (0:ℝ),tail C x' m  →  ∃K:Fin n → ℝ, J  ≤  m+1 ∧ 2*C.S.a (m+1)  <  C.S.a J ∧ (∀ k:Fin n,Drama.Wage F C (Drama.Unit C (d:=(v k).1) ((v k).snd)) (m+1+Lag n) (K k)) ∧ ∏ k:Fin n,K k ≤ x'^(-(mass v:ℝ)-ε):=by
     let δ:ℝ:= ε/(2*((Fintype.card (Fin n):ℕ)+1)); have hd:0 < δ:=div_pos hε (by positivity)
     let z(i):= ((v i).1:ℝ)+δ; let l(i m):= C.S.a (m+1+Lag n)^(-z i)
     choose m₀ _ A hp he using fun i:Fin n=>hc.centered (v i).1 δ (‖(v i).2‖+1) hd (add_pos_of_nonneg_of_pos (norm_nonneg _) one_pos) -- remove _
     have hG: Note C.S (fun m=>∏ i:Fin n,((A i+1)*l i m)) (∑ i:Fin n,z i):=by
          suffices ∀ q:Finset (Fin n), Note C.S (fun m=>∏ i∈q,((A i+1)*l i m)) (q.sum z) from this Finset.univ
          intro q; induction q using Finset.induction with
          | empty=> simpa using! Note.notes C.S 1 one_pos
          | insert i q hi ih=>
            have hq:= ((shifted (Note.note_a C.S) C.path.levels.fits.mesh (1+Lag n)).powr (-z i))
            simpa [hi,l,Nat.add_assoc] using! (((Note.notes C.S (A i+1) (by linarith only [hp i])).mills hq).mills ih|>.swapP (show 0+(-z i)*-1+q.sum z=z i+q.sum z by linarith))
     have hv (x:ℝ):Note C.S (fun m=> (Y!) m^x) (-x):= ((Local.topNote hA.notes).powr x).swapP (by ring) -- local path wrong?
     have hr:(∑ i:Fin n,z i) < (mass v:ℝ)+ε:=by
          dsimp only [z,mass,totalDeg]; rw [Finset.sum_add_distrib, show (∑ _:Fin n,δ)=(Fintype.card (Fin n):ℕ)*δ by simp]; rw [Nat.cast_sum]
          have hh:=mul_div_cancel₀ ε (show (2*((Fintype.card (Fin n):ℕ)+1):ℝ)≠0 by positivity); unfold δ; nlinarith only [hε,hh]
     have hg:=hG.outweigh (hv (-(mass v:ℝ)-ε)) (by linarith only [hr])
     have h1:= (C.S.shrinks.comp (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds (show (0:ℝ) <  C.S.a J/2 from half_pos (C.S.a_pos _)))
     filter_upwards [hg,eventually_ge_atTop J,eventually_all.mpr fun i=> eventually_ge_atTop (m₀ i),h1] with m hg hj hI hsmall x' hx heM
     refine ⟨fun i=>(A i+1)*l i m,hj.trans (Nat.le_succ _),by change 2*C.S.a (m+1)  <  C.S.a J;change C.S.a (m+1)  <  C.S.a J/2 at hsmall;linarith only [hsmall],fun i=> ?_, hg.trans (Real.rpow_le_rpow_of_nonpos hx heM.2 (by linarith [Nat.cast_nonneg (α:=ℝ) (mass v)]))⟩
     have hu:=he i (m+1+Lag n) (by specialize hI i; omega) 1 one_pos; unfold Drama.Wage; rw [Extraction.Order.fused]; apply hu.mono; intro ip hi; apply hi.mono; intro i' hu
     obtain ⟨hu,hr⟩:=hu
     obtain ⟨h1,h2⟩:=hr (v i).2 (by linarith) 0; refine ⟨hu,h1,h2.trans ?_⟩
     change _≤(A i+1)*l i m; rw [show (-(↑(v i).fst:ℝ)-δ)=-z i from by unfold z;linarith,add_one_mul]; exact add_le_add_right (show 1 ≤ l i m from Real.one_le_rpow_of_pos_of_le_one_of_nonpos (C.S.a_pos _) (by rw [Stock.a_log C.S _]; apply Real.exp_le_one_iff.mpr; linarith [RG.Shoot.scale_nn C.path.levels (m+1+Lag n)]) (by unfold z; linarith [Nat.cast_nonneg (α:=ℝ) (v i).1])) _
variable {h:ℕ}
private def error (C:Family G) (J p m:ℕ):=(2:ℝ)*(stakes C J p / pitts C m)
private lemma error_rate (C:Family G)(J p:ℕ):Note C.S (error C J p) (-1/32) := by
          rw [show (-1/32:ℝ)= -32⁻¹ from by norm_num] -- maybe
          unfold error; simpa [Local.error] using! (Local.errorNote C J p _ (by exact zero_lt_one : 0 < (1:ℝ))) -- check simp
variable (hA:Acme.Aroma C)(hT:Treasury C)(v h)
variable (lamp: Side)
include hA hT
-- Avoid Stock.Tabs name collision etc.
lemma shelf (J:ℕ): ∃ t j p, ∃ E:ℕ→ ℝ,1 < t ∧ Filter.Tendsto j atTop atTop∧ Tendsto (fun i:ℕ=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t) ∧ ∀ᶠ m in atTop,Box C J (j m) m h (fun i:Fin n=>(v i).fst) ((mass v:ℝ)-h) (fun i:Fin n=>(v i).snd) F lamp (lista C h m*(2*E m)) (error C J p m):= by
    let p := max (Stock.Tabs.mayOpen C.path.levels 1 hA.opens J).choose (C.ref h)
    obtain ⟨w',hw'⟩:=Finite.bddAbove_range (fun i:Fin n=> (C.labels.level (v i).1).coeffSize (v i).snd)
    obtain ⟨s,j,hs⟩:=hT.fees' _ (fun i:Fin n=>(v i).fst) lamp h J p 1 zero_lt_one (Stock.Tabs.open_later _ _ hA.opens ((Stock.Tabs.mayOpen C.path.levels 1 hA.opens J).choose_spec) (le_max_left ..) zero_le_one) (le_max_right ..) (1+|w'|) (show (0:ℝ)<1+|w'| from add_pos_of_pos_of_nonneg one_pos (abs_nonneg _))
    obtain ⟨_,ht,_,_,_,hj,hJ,M,_,hf⟩:=hs
    exact ⟨_,_,_, M,ht,hj,hJ,hf _ (fun i=> (hw' (Set.mem_range_self _)).trans (by linarith only [le_abs_self w'])) _⟩
omit hT in
private lemma grid_sub (a:Schedule)(k:ℕ)(w w':Cover):a.gridPoint k (w-w')=a.gridPoint k w-a.gridPoint k w':= by ext i;simp [Schedule.gridPoint]; push_cast;ring -- no hA needed
omit hA hT in
private lemma IsGrid {y:Fin n → E4}{a:Schedule}{k:ℕ}(h0:y default=0)(hX:∀i,Cord.Placed _ (a.a k) y i):∃ u:Fin n → Cover,y=a.gridPoint k ∘u ∧u default=0∧∀a:Axis,Injective (fun s=> y s a):=by
   have he(s:Fin n)(b:Axis):∃ v:ℤ, y s b=a.a k *v:= by
     by_cases h:s=default
     · exact ⟨0,by rw [h,h0,Int.cast_zero,mul_zero];rfl⟩
     exact (hX (s,b) h).1
   choose u hu using he
   have hm: y=a.gridPoint k ∘u:=by ext s i; exact hu ..
   refine ⟨u,hm,?_,fun a i j he=>?_⟩
   · ext1 i
     change u default i=0
     exact_mod_cast (mul_eq_zero.mp (show a.a k*((u default i:ℤ):ℝ)=0 from (hu default i).symm.trans (h0.symm ▸ rfl))).resolve_left (a.a_pos _).ne'
   by_contra ne; by_cases h:i=default
   · exact (hX (j,a) (h ▸ Ne.symm ne)).2 _ ne (by change y j a=y i a; exact he.symm)
   exact (hX (i,a) h).2 _ (Ne.symm ne) he
omit hT
-- extract dynamic cutoff comparator
lemma loss_box {J j m:ℕ} {B A x':ℝ}{xe:Fin n → E4} (hm: Box C J j m h (fun i=>(v i).1) ((mass v:ℝ)-(h:ℝ)) (fun i=>(v i).2) F lamp B A)(hx:tail C x' m)(hB:Cord.Band n lamp x' xe)(hp:∀ i:Fin n×Axis,Cord.Placed n (C.S.a j) xe i):
        ∃ (x:Fin n → Cover) (u:ℕ×ℕ →  C.book.Ref h)(B:ℝ), xe=C.S.gridPoint j ∘x ∧ (∀ a:Axis, Injective (fun k:Fin n=>xe k a)) ∧ (∀ᶠ k in F.fuse,‖u k‖ ≤ B) ∧ Drama.Wage F C (Drama.Loss C x v (j:=j) (charge v h m) u) J A:=by
      obtain ⟨x,hy,hr,he⟩:= IsGrid hB.1 hp
      have hsep : ∀ i j':Fin n, i≠j'→(R!) m/16 ≤ ‖C.S.gridPoint j (x i-x j')‖:= fun i j' hij=>by
         have hB:=hB.2.1 i j' hij; rw [hy] at hB; rw [grid_sub hA]; exact (hB.trans_le' (by linarith only [hx.1])).le
      have hsize : ∀ i,‖C.S.gridPoint j (x i)‖ ≤ 4*Matching.topZone C.path.levels (lamp*C.S.block m) (m+1):= fun i=>by
         obtain hx':= hB.2.2 i; rw [hy] at hx'; refine hx'.le.trans ?_
         rw [topZone,show (lamp*C.S.block m).val=lamp.val*(C.S.block m).val from rfl,Nat.cast_mul]; change 4*lamp.val*x' ≤ 4*(lamp.val*(C.S.block m).val*fuga _ _); have :=Nat.cast_nonneg (α:=ℝ) lamp.val; obtain ⟨-,hR⟩:=hx; change x'≤(C.S.block m).val*(fuga _ _) at hR; nlinarith only [mul_le_mul_of_nonneg_left hR this]
      obtain ⟨b,hb⟩:=hm.corners x hr hsep hsize
      refine ⟨x,b,B,hy,he,?_ ,?_⟩
      · rw [Extraction.Order.fused]; refine hb.mono fun j hj=>hj.mono ?_
        rintro i ⟨h,hx'⟩;exact hx'.1
      unfold Drama.Wage; rw [Extraction.Order.fused]; apply hb.mono; intro i hi; apply hi.mono; intro s hs; refine ⟨hs.choose, hs.choose_spec.2⟩
include hT
lemma portion (J:ℕ) {ε:ℝ}(hε:0 < ε) (hc:CellHyp C F):∃ A:ℕ→ℝ, ∃ t j, 1 < t ∧ Filter.Tendsto j atTop atTop∧ Tendsto (fun i:ℕ=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t) ∧ Note C.S A (-1/32) ∧ ∀ᶠ m in atTop, Portion C F h v J m (j m) lamp ε (A m):=by
     obtain ⟨t,j,p,E,ht,hj,hJ,hm⟩:=shelf (F:=F) v h hA hT lamp J
     let e:=error C J p
     -- 
     refine ⟨e,t,j,ht,hj,hJ,error_rate _ _ _,?_⟩
     filter_upwards [hm,micro_budget (v:=v) hε hc hA (J:=J), ((Local.topNote hA.notes).thins (by norm_num)|>.const_mul (8*(4*(lamp.val:ℝ)))).eventually (gt_mem_nhds (show (8*(4*(lamp.val:ℝ)))*(0:ℝ)<C.S.a J by rw [mul_zero];apply C.S.a_pos))] with m hv hK hsmall
     refine ⟨fun r hr hx xe hX hp=>loss_box v h hA lamp hv hx hX hp,hK,fun r hr hx xe hX s=>?_⟩
     calc _ ≤ 8*(4*lamp.val*r):= mul_le_mul_of_nonneg_left ((hX.2.2 s).le) (by norm_num)
          _ ≤ 8*(4*lamp.val)*(Y! m):=by have h:=hx.2; change r ≤ _ at h; nlinarith only [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α:=ℝ) lamp.val)]
          _ < _:= hsmall
end YM.MultipleContact.ScheduleRow
