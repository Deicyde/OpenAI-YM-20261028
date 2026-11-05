import YM.OPE.Cards.Literal
import YM.Work.B15
import YM.Work.B16
import YM.MergeProof.North.Brim

/-!
# Geometry along long lifts at cutoff

Work at arbitrary snapshot, both placement budget and grid level announced;
each regulator limit is afforded with the full test inequality on that regulator
(separation tested *after* modular wrapping). No budget on the number of
replicas at this level of the charge; two sizing inequalities only charge for
the arities of the main packet and exterior of one copy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cards
open Function Filter Set Lattice Cells Wilson Extraction Word Next.Phase
open MergeProof Ribbons Work Next.Rank Station Bid
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{S:Schedule} {ι κ : Type*}[Fintype ι][Fintype κ]
    {φ : Extraction.Order}
variable {N p k k' b l : ℕ} (e:b ≤ k) (K : ℕ) (P : Points K) {g h : Cover}
variable (t : ℕ) (x y z : Cover)
lemma sameResidue {p:Side} (T : Tiling p)(s : Cover) (x : Site p){t:ℕ}(h:T.side.val ∣ t) :
    ∀ i,stripe T (x + wrap p (t • s)) i=stripe T x i:=by
    intro i; have he: ((t:ℕ):Per T.side)=0:= by obtain ⟨u,hu⟩:=h; rw [hu,Nat.cast_mul,ZMod.natCast_self,zero_mul]
    unfold stripe; rw [map_nsmul]; simp only [Pi.add_apply,Pi.smul_apply]; simp only [nsmul_eq_mul,map_sub,map_add,map_mul,map_natCast,he,zero_mul, add_zero]
lemma invariantMargins {W : Tiling (C.S.side N p)}(hn:k≤N)(hW: W.kind=.link) (hd:W.side.val∣ Cells.span C.S (e.trans hn) p) (j:ℕ)(hp:Inside W K (location C.S k N p x)) :
    Inside W K (location C.S k N p (x+Episode.step C e t j)):=by
    rw [Order.location_add,← B15.addr_root C e hn]; rw [inside_stripe _ hW];
    have hi := (inside_stripe _ hW _ _).1 hp; let T:=center C.S p (e.trans hn) 0
    intro i; rw [show T.units.root (B15.addr T t j)=_ from (by unfold B15.addr; rw [Ratio.root_embed,T.units.embed_wrap]; rfl : T.units.root (B15.addr T t j) = wrap (C.S.side N p) ((Cells.span C.S (e.trans hn) p) • B15.diag t j)), sameResidue W _ _ hd]; exact hi i
-- separate in Euclidean norm, until snapshot condition consumed.
-- prefer simple bound 2 * S.a b vs actual distance (rather than cube), used for rate conversion anyway.
lemma native_space (C:Family G)(x y : Cover){k:ℕ} : ∀ᶠ p:ℕ in atTop, ‖C.S.gridPoint k x - C.S.gridPoint k y‖ ≤
     2*(C.S.a k * (separation (wrap (C.side k p) x) (wrap (C.side k p) y) :ℝ)) :=by
    filter_upwards [faraway C k (x-y)] with p hp
    let V := wrap (C.side k p) (x-y); rw [show C.S.gridPoint k x-C.S.gridPoint k y=C.S.gridPoint k (x-y) from (by have hi:= B16.grid_add (C:=C) (k:=k) (x-y) y; rw [sub_add_cancel] at hi; exact eq_sub_of_add_eq hi.symm|>.symm), ← hp];
    have ht:separation V 0= separation (wrap (C.side k p) x) (wrap (C.side k p) y):=by unfold separation V; rw [sub_zero,map_sub]
    exact (normC C k p V|>.2).trans_eq (by rw [ht,mul_assoc])
lemma lock_space (C:Family G)(W:ℕ) (x y:Cover)(he:2*C.S.a W< ‖C.S.gridPoint k x-C.S.gridPoint k y‖) :
    ∀ᶠ i: ℕ×ℕ in φ.fuse, ∀ hi:W ≤ i.1, Cells.span C.S hi i.2 < separation (location C.S k i.1 i.2 x) (location C.S k i.1 i.2 y):=by
    rw [Order.fused,Order.late]; filter_upwards [φ.per.cofinal.eventually (native_space (k:=k) C x y)] with p hp
    filter_upwards [φ.mesh.cofinal.eventually_ge_atTop k] with N hN hW; let n:=φ.mesh N; let q:=φ.per p
    have hm:k≤ n:=hN; let S:= C.S.toDepth hm q; let L:= S.count.val; let M:= separation (wrap (C.side k q) x) (wrap (C.side k q) y)
    have ht: ((L*M:ℕ):ℝ)*C.S.a n=C.S.a k*M:=by rw [Nat.cast_mul,mul_comm _ (C.S.a n),← mul_assoc]; congr 1; exact C.S.embeds_scale S
    rw [Cells.location,Cells.location,dif_pos hm,dif_pos hm, Station.both]; apply (Nat.cast_lt (α:=ℝ)).1; change (Cells.span C.S hW q:ℝ) < (↑(L*M:ℕ):ℝ); apply lt_of_mul_lt_mul_right _ (C.S.a_pos n|>.le)
    rw [ht,mul_comm _ (C.S.a n),show C.S.a n *_= _ from C.S.embeds_scale (C.S.toDepth hW q)]
    linarith only [he.trans_le hp]
local notation "Y" => C.S.gridPoint

lemma car_space {b k:ℕ} (e:b≤k)(C:Family G)(Q:ℝ)(x y:Cover){i j:ℕ}(hb:i≠j) : ∀ᶠ t:ℕ in atTop,Q < ‖C.S.gridPoint k (x+Episode.step C e t i)-C.S.gridPoint k (y+Episode.step C e t j)‖:=by
    -- don't include ambient notation
    let h u v:=‖C.S.gridPoint k u-C.S.gridPoint k v‖; let S:= C.S.gridPoint k; let A(z:ℕ)(t):= Episode.step C e t z
    have hf(w v:Cover) (i j:ℕ) (he:i < j) : ∀ᶠ t : ℕ in atTop,Q < h (w+A i t) (v+A j t):=by
       let a:=timeAxis; let y(x:Cover):=(S x) a
       have hp: Tendsto (fun t:ℕ=> y (A j t)-y (A i t)) atTop atTop:=by
          have hz:=mul_pos (mul_pos (C.S.a_pos k) (by exact_mod_cast (C.S.toDepth e 0).count.property : 0 < ((C.S.toDepth e 0).count.val:ℝ))) (mul_pos (a:= (2:ℝ)) (by norm_num) (show 0< (j:ℝ)-(i:ℝ) from sub_pos.mpr (by exact_mod_cast he)))
          refine (Tendsto.atTop_mul_const hz (tendsto_natCast_atTop_atTop (R:=ℝ))).congr fun t=>?_; unfold y S A; simp [Schedule.gridPoint,Episode.step]; ring
       filter_upwards [hp.eventually_gt_atTop (Q+y w-y v)] with t ht; unfold h
       refine lt_of_lt_of_le (b:= ‖(C.S.gridPoint k (v+ A j t) - C.S.gridPoint k (w + A i t)) a‖) ?_ (by rw [norm_sub_rev (C.S.gridPoint k (w + A i t))]; exact PiLp.norm_apply_le (S _-S _) a)
       change Q< ‖(C.S.gridPoint k (v+ A j t) - C.S.gridPoint k (w + A i t)) a‖; rw [B16.grid_add,B16.grid_add,PiLp.sub_apply,PiLp.add_apply, PiLp.add_apply];
       apply lt_of_lt_of_le (b:=y v+y (A j t)-(y w+y (A i t))) _ (Real.le_norm_self _); linarith only [ht]
    rcases lt_or_gt_of_ne hb with h|h; · exact hf x y i j h
    filter_upwards [hf y x j i h] with t ht; rw [norm_sub_rev]; exact ht
lemma car_space_same {b k:ℕ} (e:b ≤ k)(C:Family G)(Q:ℝ)(x y:Cover) {i t:ℕ}(hb:Q<‖C.S.gridPoint k x-C.S.gridPoint k y‖) : Q < ‖C.S.gridPoint k (x+Episode.step C e t i)-C.S.gridPoint k (y+Episode.step C e t i)‖:=by
    rw [B16.grid_add,B16.grid_add,add_sub_add_right_eq_sub]; exact hb

set_option quotPrecheck false
local notation "R" => C.side N p
lemma seats (C:Family G)(hk:k ≤ N) (hb:b ≤ k)(hl:k ≤ l)(he:l≤k') (hN:k' ≤ N) (u:ι→Site (C.side N p))(v:κ→Site (C.side N p))
    (hI:(Fintype.card ι:ℝ)*(2*(5*C.S.a k)) < C.S.a b)(hE:(Fintype.card κ:ℝ)*(2*(3*C.S.a k')) < C.S.a l):
      ∃ x: Site (C.side N p), let T:= (center C.S p (hb.trans hk) 0).newly x; let W:= (center C.S p (he.trans hN) 0).newly x; (∀ i, Inside T (3*Cells.span C.S hk p) (u i)) ∧
          ∀ i, Inside W (3*Cells.span C.S hN p) (v i) :=by
    -- adapt `Passage.margins`: only one native resolution consumed. hN implies hk.
    let T:=center C.S p (hb.trans hk) (0:Site (C.S.side N p)); let Y':= center C.S p (he.trans hN) (0:Site (C.S.side N p)); let d:= Cells.span C.S hk p; let r:=Cells.span C.S hN p
    have room_cast {f k} (h:f≤k)(hk:k≤N) (n L:ℕ)(hp: (n:ℝ)*(2*((L:ℝ)*C.S.a k)) < C.S.a f): n*(2*(L*Cells.span C.S hk p))< Cells.span C.S (h.trans hk) p:=by
       apply (Nat.cast_lt (α:=ℝ)).mp; apply lt_of_mul_lt_mul_left _ (C.S.a_pos N).le; have hh a (ha:a≤N) : C.S.a N*Cells.span C.S ha p=C.S.a a:= C.S.embeds_scale (C.S.toDepth ha p)
       rw [hh]; rw [← hh k hk] at hp; push_cast; linarith
    obtain ⟨o,ho⟩:=T.fits_together (u ∘ (Fintype.equivFin ι).symm) (5*d) (Nat.mul_pos (by decide) (C.S.toDepth hk p).count.property) (room_cast hb hk _ _ (by exact_mod_cast hI))
    obtain ⟨w,hw,hF⟩:= shift_into Y' v o rfl (3*r) (Nat.mul_pos (by decide) (C.S.toDepth hN p).count.property) (room_cast he hN _ _ (by exact_mod_cast hE))
    have hG:Y'.side.val ≤ d:= Nat.le_of_dvd (C.S.toDepth hk p).count.property (Around.inherits hl (he.trans hN))
    refine ⟨_, fun i=> ?_, hF⟩; let X:= T.newly o; have hh : Inside X (5*d) (u i):=by simpa [Next.Phase.Inside, X] using ho ((Fintype.equivFin ι) i)
    have hp:= inside_after X rfl _ w 0 d hh (fun a=>(hw a).le.trans hG) (fun a=>by simp)
    simp only [map_zero,add_zero] at hp; exact hp
end YM.OPE.Cards
