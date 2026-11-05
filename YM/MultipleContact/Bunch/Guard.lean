import YM.MultipleContact.Bunch.Cord
import YM.MultipleContact.Matching.Arena
/-! Kinematics of comparable arbitrary products and their genuine field derivatives. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 500000
noncomputable section
namespace YM.MultipleContact.Bunching.Guard
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Ribbons Around Cells Wilson Lattice Climb Set
open scoped Topology BigOperators Classical ContDiff
open YM.Next.UVStress Matching Local Cord Acme WithLp
variable {G:Gauge}{C:Family G}{n':ℕ} [Inhabited (Fin n')]
variable {ι:Type*}[Fintype ι]{n:ι→ℕ}
variable (K:Set ((i:ι)→Points (n i)))(hK:IsCompact K)(hsafe:∀x∈K,∀i, Points.cons 0 (x i) ∈ conf (n i+1))
variable (hw:Note C.S (fun i=>fuga C.path.levels (i+1)) (-1))
set_option quotPrecheck false
local notation "R'" => (fun i:ℕ=> fuga C.path.levels (i+1))
local notation "Yb" => (fun i:ℕ=> topZone C.path.levels (C.S.block i) (i+1))
include hsafe hw hK
lemma fits (L:Lattice.Side):∀ᶠ m in atTop, ∀ (r:ℝ), (R') m ≤ r → r≤ (Yb) m → ∀ z∈K,∀ y:Fin n'→E4,Cord.Band n' L r y →∀i,slide C.S (m+1) (lands y (z i)):=by
   obtain ⟨δ,hδ,hp⟩:=Local.gapK K hK hsafe
   filter_upwards [((Local.topNote hw).thins (show -(1:ℝ)<0 by norm_num)|>.const_mul (8*(L.val:ℝ))).eventually (gt_mem_nhds (show 8*L.val*(0:ℝ)<δ by simpa using hδ))] with m hm r hr hr' z hz y hy i
   have hr0:0<r:=(hw.pos m).trans_le hr
   have hδm: 8* (L.val:ℝ)*((Yb) m) < δ:=hm
   have hLpos:0<(L.val:ℝ):=by exact_mod_cast L.pos
   have hδ': 5*(L.val:ℝ)*r<δ:= (mul_lt_mul_of_pos_right (show 5*(L.val:ℝ)<8*(L.val:ℝ) from (by linarith only [hLpos])) hr0).trans (hδm.trans_le' (mul_le_mul_of_nonneg_left hr' (by positivity)))
   have hb:(1:ℝ)≤ (C.path.levels.budget (m+1)).B := by exact_mod_cast (C.path.levels.budget (m+1)).B_pos
   have hd:=C.S.a_pos (m+1)
   have hwa:4*C.S.a (m+1) ≤ r/32:=by change 128*_*(C.S.a _ ) ≤ _ at hr; nlinarith only [hr,mul_le_mul_of_nonneg_right (one_le_pow₀ hb (n:=2)) hd.le,hd]
   have h1 s:lands y (z i) (Fin.castAdd (n i) s)=y s:=Fin.append_left ..
   have h2 s:lands y (z i) (Fin.natAdd n' s)=z i s:= Fin.append_right ..
   have hx(k:Fin (n i)): δ<‖z i k‖:=by
       have hx:= hp z hz i k.succ 0 k.succ_ne_zero; simpa only [Points.cons,points_apply,Fin.cons_zero,Fin.cons_succ,sub_zero] using hx
   have hβ: r ≤ (L.val:ℝ)*r:= le_mul_of_one_le_left hr0.le (show (1:ℝ)≤L.val from Nat.one_le_cast.mpr L.pos)
   intro s t; revert t; refine Fin.addCases (fun s t=>?_) (fun s t=>?_) s
   · refine Fin.addCases (fun u h=>?_ ) (fun v _=>?_) t
     · rw [h1,h1]; have hx:=hy.2.1 u s (show u≠s from fun e=>h (e ▸ rfl)); linarith only [hwa,hx,hr0]
     rw [h2,h1]; nlinarith only [hr0,hLpos,hwa,hδ',hβ,hy.2.2 s,hx v,norm_sub_norm_le (z i v) (y s)]
   refine Fin.addCases (fun u _=>?_) (fun v h=>?_) t
   · rw [h1,h2,norm_sub_rev]; nlinarith only [hr0,hLpos,hwa,hδ',hβ,hy.2.2 u,hx s,norm_sub_norm_le (z i s) (y u)]
   rw [h2,h2]; nlinarith only [hr0,hLpos,hwa,hδ',hβ,show δ<‖z i v-z i s‖ from hp z hz i v.succ s.succ (fun e=>h (by rw [Fin.succ_inj.mp e]))]

lemma onGrid {y:Fin n' → E4}{m:ℕ} (h0:y default=0)(hp:∀i,Cord.Placed _ (C.S.a m) y i):∃ u:Fin n' → Cover,y=C.S.gridPoint m ∘u ∧u default=0∧∀a:Axis,Injective (fun s=> y s a):=by
   have he(s:Fin n')(a:Axis):∃ v:ℤ, y s a=C.S.a m*v:= by
     by_cases h:s=default
     · exact ⟨0,by rw [h,h0,Int.cast_zero,mul_zero];rfl⟩
     exact (hp (s,a) h).1
   choose u hu using he
   have hm: y=C.S.gridPoint m ∘u:=by ext s a; exact hu ..
   refine ⟨u,hm,?_,fun a i j he=>?_⟩
   · ext1 a
     change u default a=0
     exact_mod_cast (mul_eq_zero.mp (show C.S.a m*((u default a:ℤ):ℝ)=0 from (hu default a).symm.trans (h0.symm ▸ rfl))).resolve_left (C.S.a_pos _).ne'
   by_contra ne; by_cases h:i=default
   · exact (hp (j,a) (h ▸ Ne.symm ne)).2 _ ne (by change y j a=y i a; exact he.symm)
   exact (hp (i,a) h).2 _ (Ne.symm ne) he
end YM.MultipleContact.Bunching.Guard

namespace YM.MultipleContact.Bunching.Line
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Ribbons Around Cells Wilson Lattice Climb Set
open scoped Topology BigOperators Classical ContDiff
open YM.Next.UVStress Matching Local Cord Acme WithLp
variable {G:Gauge}{C:Family G}{n':ℕ}
variable {ι:Type*}{n:ι→ℕ}
variable {S:Table C.book}(V:Fin n'→S.Tag)
-- indexed changed tag at slot k after j derivatives
def tags (W:DiffPlan S)(k:Fin n')(b:Axis)(j:ℕ):= Function.update V k (trek W b (V k) j)
private lemma tags_step (W:DiffPlan S)(k:Fin n')(b:Axis)(j:ℕ): tags V W k b (j+1)=Function.update (tags V W k b j) k (Ward.rise W b ((tags V W k b j) k)):=by unfold tags; rw [Function.update_self,Function.update_idem]; rfl
lemma whole_update {m:ℕ}(w:Fin m →S.Tag)(W:DiffPlan S)(k:Fin n')(b:Axis)(j:ℕ):let f(j:ℕ):=Fin.append (tags V W k b j) w; f (j+1)=Function.update (f j) (Fin.castAdd m k) (Ward.rise W b ((f j) (Fin.castAdd m k))):=by
   intro f; unfold f; rw [Fin.append_left,tags_step]; funext s; refine Fin.addCases (fun u=>?_) (fun u=>?_) s
   · rw [Fin.append_left]; by_cases h:u=k
     · simp only [h,Function.update_self]
     rw [Function.update_of_ne h,Function.update_of_ne (show Fin.castAdd m u≠Fin.castAdd m k from Fin.castAdd_injective n' m |>.ne h)]; exact (Fin.append_left ..).symm
   rw [Fin.append_right,Function.update_of_ne (show Fin.natAdd n' u≠Fin.castAdd m k from (by intro h; have h:=congr_arg Fin.val h; simp at h; omega)),Fin.append_right]
variable (q:∀i:ι,Fin (n i)→ C.book.Token) (W:DiffPlan S) (H:S.Hierarchy)(hp:W.Derivatives S)
omit V in
lemma path (k:Fin n'×Axis)(x:Fin n'→E4)(u:ℝ)(i:ι)(z:Points (n i)): lands (Cord.polar k x 1 u) z= lands (Cord.polar k x 1 0) z+ u • Points.direction (Fin.castAdd (n i) k.1) k.2:=by
   ext1 j; change (lands (Cord.polar k x 1 u) z) j= _
   refine Fin.addCases ?_ ?_ j; swap
   · intro a
     have ht: Fin.castAdd (n i) k.1 ≠ Fin.natAdd n' a:=fun e=> by have e:=congr_arg Fin.val e; simp at e; have h:=k.1.isLt; omega
     simp [lands,Points.direction,PiLp.single_apply,ht]
   intro a; by_cases ha:a=k.1
   · simp [lands,Points.direction,PiLp.single_apply,ha,Cord.polar,Cord.streak,Ward.inc]
   have ht: Fin.castAdd (n i) k.1≠Fin.castAdd (n i) a:=by intro he; apply ha; exact (Fin.castAdd_injective n' (n i)) he.symm
   simp [lands,Cord.polar,Points.direction,PiLp.single_apply,ha,ht]
include H hp
lemma deriv (x:Fin n'→E4)(a:ℝ)(j:Fin n')(b:Axis)(z:∀i,Points (n i))(i:ι) (t:ℝ) (hv:lands (Cord.polar (j,b) x a t) (z i) ∈conf _) (l:ℕ):
   HasDerivAt (fun u:ℝ=>(a^l:ℝ) • many (tags V W j b l) (q i) (Cord.polar (j,b) x a u) (z i))
      ((a^(l+1):ℝ) • many (tags V W j b (l+1)) (q i) (Cord.polar (j,b) x a t) (z i)) t:=by
   have hx : HasDerivAt (fun v:ℝ=> v*a) a t:=by simpa using (hasDerivAt_id' t).mul_const a
   let p:= Fin.castAdd (n i) j; let d:= Points.direction p b
   let h u:= lands (Cord.polar (j,b) x 1 u) (z i); let w l:= Fin.append (tags V W j b l) (S.classTokens∘q i)
   have heq(v):Cord.polar (j,b) x a v=Cord.polar (j,b) x 1 (v*a):=by unfold Cord.polar Cord.streak; simp only [mul_one]
   rw [heq] at hv; simp_rw [heq];
   have hh: HasDerivAt h (Points.direction p b) (t*a):=by
       rw [show h=(fun u=>h 0+u • d) from funext (path (j,b) x · i (z i))]
       apply (hasDerivAt_const_add_iff _).mpr
       exact (show HasDerivAt (ContinuousLinearMap.toSpanSingleton ℝ d) _ _ from
             (ContinuousLinearMap.toSpanSingleton ℝ d).hasDerivAt.congr_deriv (by simp; rfl))
   have hq := ((cont_disc H (w l) hv).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (t*a) hh
   have hD:= fromD W H hp hv p b (w l)
   rw [pow_succ, ← smul_smul]
   convert (hq.scomp t hx).const_smul (a^l) using 1
   all_goals first |rfl| skip
   change _ = (_ : ℂ)
   unfold many; unfold w
   have hw := whole_update V (S.classTokens∘q i) W j b l
   change (fderiv ℝ (disc (w l)) (h (t*a))) (Points.direction p b) = disc (update (w l) p _) _ at hD
   change w (l+1)=update (w l) p (Ward.rise W b _) at hw
   exact congr_arg (fun x:ℂ=> a^l • (a • x)) ((congr_arg (fun v:Fin _→ S.Tag=>disc v (h (t*a))) hw).trans hD.symm)
end YM.MultipleContact.Bunching.Line
