import YM.RG08.Ducat.Castle
/-! # Geometry grades for strict remainder, literal equalities.
 Min width λ for all predecessors fine? improve using farm cost V=Σ individual. -/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{O:Type}{I J:O→Type}{n m k e u r i:ℕ}{D:Exchange O}{d v:O→ℝ}{w:ℕ→ℕ→O→ℝ}{P:O→ RG.Patch}{K:RG.KernelChoices}{A B:O→Castle G}

private lemma sum_box {I:Type}{P:RG.Patch}(s:Finset I)(H:I→Flake n (Market (Loc G 1))):Cairn.box P (∑ i∈s,H i)=∑ i∈s,Cairn.box P (H i):=by
 induction s using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty,box_nil]
 | @insert a s ha he=>
   rw [sum_insert ha,sum_insert ha]
   have ht:=Cairn.box_sub P (H a+s.sum H) (H a);rw [add_sub_cancel_left,he] at ht;exact (sub_eq_iff_eq_add.mp ht.symm).trans (add_comm ..)

private lemma lance_earlier (he:∀ a q x,0<w a q x)(hd:∀ x,0≤d x)(hv:∀ x,0<v x)(hz:∀ x,v x ≤ 1)(hA:Book D A B w d e r)(ha:∀ x,Fair (A x))(hb:∀ x,Fair (B x))(hP:D.Good fun x=>poem G m k (w i m x))(hk:0<k)
    (hu:∀ x,v x ≤ ((P x).L.val:ℝ)*(trail m (w i m) x))(ht: i = u ∧ k = RG08.Mount.rank m → u = e → r < m)(hU:i ≤ u)(hE:u ≤ e):
 Lance (I:=fun x=>Tack.Head (P x) G) D v d (fun x=>Cairn.box (P x) (RG08.Mount.flight m i (A x m i) u k)) (fun x=>Cairn.box (P x) (RG08.Mount.flight m i (B x m i) u k)):=Ducat.box hv hd P (seniors he hd hA ha hb hP hk (hU.trans hE) ht hE hU) hu hz -- check argument order

-- strips at fine widths: after owning gate sale for each deterministic insurance. Covers e=r same lane too to simplify.
structure Quarrying (D:Exchange O)(P:O→RG.Patch)(w:ℕ→ℕ→O→ℝ)(v:O→ℝ)(e:ℕ)(h:∀ x,(P x).Branches K G)(Z:ChartRatio G):Prop where
 roof : ∀ x, 0<v x∧v x≤1
 fresh:∀ i r x,0<w i r x
 meet (i r:ℕ): i ≤ e→ r ≤ i→ ∀ x,v x ≤ ((P x).L.val:ℝ) * trail r (w i r) x
 duty k:k ≤ e+2 → Slice (G:=G) v e k D w
 crush k:k ≤ e+2→D.Good fun x=>max 0 (park (h x) k (v x))
 hail k:k ≤ e+2→D.Good fun x=> max 0 (Cairn.layer Z (v x) k)

lemma harmless (h:∀ x,(P x).Branches K G)(Z:ChartRatio G)(hK:Quarrying D P w v e h Z)
    (hk:k ≤ e+2): Lance (I:=fun x=>Tack.Head (P x) G) D v d (fun x=> -bell (h x) u k+dusk (P x) Z u k) (fun x=> -bell (h x) u k+dusk (P x) Z u k):=by
   apply Bound.join
   refine ⟨_,D.hear _ _ (hK.crush k hk) (D.moreover _ _ (Ducat.exp_price (fun x=>(hK.roof x).2)) (hK.hail k hk)),?_⟩
   intro x
   let a:=max 0 (park (h x) k (v x));let b:=max 0 (Cairn.layer Z (v x) k)
   have ha:Held (carpet _) (v x) a (bell (h x) u k):=by
      unfold RG08.Mount.bell;split
      next =>exact (parade_bill (h x) k (σ:=v x)).1.mono le_rfl (le_max_right ..) (fun _=>le_rfl)
      next=>exact zero_held
   have he:0≤v x :=(hK.roof _).1.le
   have ht:Held (carpet _) (v x) (Real.exp (8*v x)*b) (dusk (P x) Z u k):=by
      unfold dusk;split <;> first|exact zero_held| skip
      exact Cairn.box_cost ((Cairn.vanity_bill Z k (σ:=v x)).1.mono le_rfl (le_max_right ..) (fun _=>le_rfl)) he _
   exact (ha.neg).add ht (le_max_left ..) (mul_nonneg (Real.exp_nonneg _) (le_max_left ..))

-- fine positive terms at all predecessors of (e,r), and at self pull Γ through removal.
lemma eligible_lane (h:∀ x,(P x).Branches K G)(Z:ChartRatio G)(hK:Quarrying D P w v e h Z)(hk:Book D A B w d e r)(ha:∀ x,Fair (A x))(hb:∀ x,Fair (B x))(hd:∀ x,0 ≤ d x) {m i:ℕ} (hp:Steam.Residual e (RG08.Mount.rank r) m i):
 Lance (I:=fun x=> Tack.Head (P x) G) D v d (fun x=> inlet (h x) (A x) Z m i) (fun x=> inlet (h x) (B x) Z m i):=by
   unfold Steam.Residual Steam.taps at hp; obtain ⟨hi,hM,H,hP⟩:=hp
   unfold inlet ghost RG08.Mount.sweep castle demand; simp_rw [if_pos hM]
   let g(x:O):=bell (h x) m i;let f(x:O):=dusk (P x) Z m i
   have hx (x)(y:Flake i (Market (Head (P x) G))): -(y+g x)+f x= -y+(-g x+f x):=by abel
   change Lance _ _ _ (fun x=> -(_+g x)+f x) (fun x=> -(_+g x)+f x)
   simp_rw [hx]
   refine Lance.add (Lance.opposite ?_) (harmless h Z hK (k:=i) (by unfold RG08.Mount.rank at *;omega)) hd
   -- box nested
   simp_rw [sum_box]
   apply Lance.series _ _ _ _ hd; intro a hx;apply Lance.series _ _ _ _ hd;intro r hr -- binder confusion
   -- r shadow original, rename inaccessible original and hx from local terms?
   have ha': a ≤ e:=by simp only [mem_range] at hx;omega
   have hr':r ≤ a:=by simpa using hr
   apply lance_earlier hK.fresh hd (fun i=>(hK.roof i).1) (fun i=>(hK.roof i).2) hk ha hb (hK.duty i (by omega) a r ha' hr') hi (hK.meet _ _ ha' hr') _ _ _
   · intro hg he; unfold RG08.Mount.rank at *;omega
   all_goals simp only [mem_range] at *;omega
-- residual self e,n minus repeated source. Unfold using `curtain` remove same input grade (not assuming other grades known same lower rank; they cannot appear).
def curtain (A: Castle G)(e:ℕ): Scroll G:=fun i k=> ∑ a∈ Finset.range e, ∑ p∈ range (a+1),RG08.Mount.flight p a (A p a) i k
lemma self_demand (V:Castle G)(k e:ℕ): demand V e (RG08.Mount.rank k)= curtain V e e (RG08.Mount.rank k)+ if k ≤ e then completed (V k e) (stick k) (RG08.Mount.rank k) else 0:=by
 unfold demand;rw [Finset.sum_range_succ];apply congrArg
 split_ifs with h
 · rw [Finset.sum_eq_single_of_mem k (by simpa) (fun i _ hi=>?_),Sedan.flight_start,dif_pos rfl]
   · rfl
   rw [flight_start,dif_neg (by intro hv;apply hi;unfold RG08.Mount.rank at hv;omega)]
 apply Finset.sum_eq_zero; intro i hi;rw [flight_start,dif_neg (by simp only [mem_range] at hi;unfold RG08.Mount.rank;omega)]

/-- rest at self e,n. compare strictly only. -/
def mine {b:RG.Patch}(h:b.Branches K G)(A:Castle G)(Z:ChartRatio G)(e r:ℕ):Flake (RG08.Mount.rank r) (Market (Tack.Head b G)):= -(Cairn.box b (curtain A e e (RG08.Mount.rank r)) + bell h e (RG08.Mount.rank r))+dusk b Z e (RG08.Mount.rank r) -- B binder wrong
lemma self_inlet {t:Patch}(h:t.Branches K G)(A:Castle G)(Z:ChartRatio G)(ha:0<e)(ht:r ≤ e):
 inlet h A Z e (RG08.Mount.rank r)=mine h A Z e r-Cairn.box t (completed (A r e) (stick r) (RG08.Mount.rank r)):=by
 unfold inlet ghost RG08.Mount.sweep castle;rw [if_pos ha]; change -(Cairn.box _ (demand A _ _) +_)+_= _
 rw [self_demand,if_pos ht];unfold mine
 let F:=curtain A e e (RG08.Mount.rank r);let V:=completed (A r e) (stick r) (RG08.Mount.rank r)
 have ht':= Cairn.box_sub t (F+V) V;rw [add_sub_cancel_right] at ht'
 rw [show Cairn.box _ (F+_) = _ from (sub_eq_iff_eq_add.mp ht'.symm)];abel -- orientation?

lemma self_lane (h:∀ x,(P x).Branches K G)(Z:ChartRatio G)(hK:Quarrying D P w v e h Z)(hk:Book D A B w d e r)(ha:∀ x,Fair (A x))(hb:∀ x,Fair (B x))(hd:∀ x,0 ≤ d x) (hr:r ≤ e):
 Lance D v d (I:=fun x=>Tack.Head (P x) G) (fun x=>mine (h x) (A x) Z e r) (fun x=>mine (h x) (B x) Z e r):=by
 let n:=RG08.Mount.rank r;let f(x:O):=bell (h x) e n;let f₀(x:O):= dusk (P x) Z e n;have he:n ≤ e+2:=by unfold n RG08.Mount.rank;omega
 have hx (x)(y:Flake n (Market (Tack.Head (P x) G))) : -(y+f x)+f₀ x= -y+(-f x+f₀ x):=by abel
 unfold mine;change Lance _ _ _ (fun x=> -(_+f x)+f₀ x) (fun x=> -(_+f x)+f₀ x)
 simp_rw [hx];refine Lance.add (Lance.opposite ?_) (harmless h Z hK he) hd
 unfold curtain;simp_rw [sum_box];apply Lance.series _ _ _ _ hd;intro i hi;apply Lance.series _ _ _ _ hd;intro k hk'
 have h1:k ≤ i:=by simpa using hk'
 have h2:i<e:=by simpa using hi
 exact lance_earlier hK.fresh hd (fun i=>(hK.roof i).1) (fun i=>(hK.roof i).2) hk ha hb (hK.duty n he i k h2.le h1) (by unfold RG08.Mount.rank;omega) (hK.meet _ _ h2.le h1) (fun h _=>by have :=h.1;omega) h2.le le_rfl
end YM.RG08.Ducat
