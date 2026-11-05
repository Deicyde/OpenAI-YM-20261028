import YM.RG08.Creek.Books
/-! # Combining determined test profile with all-root cost, exact $Load$ and preimage sum. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door Analysis
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Summit Wings High Pill Taste Run PowerSeries
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I:Type}[Fintype I][DecidableEq I]{G:Gauge}{X:Chain}{m N k i j t D:ℕ}{R:ℝ}{a b:I→ℕ}{p:List I}
section book
-- if $in t$ slot vanishes then its speak. independent of separated constraints
private lemma spoke_z {x:I→ Sight D R}{T: Finset I}{a:I}(hp:a∈T)(h:x a=0) : speak T x=0:=by
   apply (Scouts.tie T D R).injective; apply Subtype.ext; refine ContinuousMap.ext fun y=> ?_
   refine Finset.prod_eq_zero (s:=univ) (f:=fun i:↥T=> (x i.val).val (y i.val).1 (y i.val).2) (mem_univ (⟨_,hp⟩:↥T)) ?_
   dsimp only; rw [h]; rfl
lemma slight (V:Layouts I G D R)(q:Places I)(b:I→Sight D R)(i:I)(ht:b i=0) (t:Finset I)(hp:i∈t): SolarPaper V q b t=0 := by
    induction t using strongInductionOn with
    | _ t ih=>
       unfold SolarPaper Fabrics; rw [Wax.banner, if_neg (Finset.nonempty_iff_ne_empty.mp ⟨i,hp⟩)]; refine Eq.trans (congr_arg (_ • ·) (sum_eq_zero ?_)) (smul_zero _)
       intro j hj
       have hk:= ((mem_filter.mp j.property).1 : j.val∈partners t); have hh:= (norms_par t j.val).mp hk
       by_cases h:i∈j.val.1
       · rw [show sons (Wax.access b (V q)) j.val.1=0 from Eq.trans (congr_arg ((↑j.val.1.card:ℝ) • ·) (show access b (V q) j.val.1=0 from funext fun u=>funext fun p=>funext fun q'=> (_: sampleK j.val.1 b _=0))) (smul_zero _),gust_z]
         intro u p y; exact (congr_arg _ (spoke_z h ht)).trans (map_zero (V q j.val.1 _ _ _))
       rw [show Wax.banner j.val.2 (access b (V q)) gust (spine_one (Loc G 1))=0 from ih j.val.2 (part_lt j.property) (Or.resolve_left (mem_union.mp (hh.1 ▸ hp)) h)]
       funext k; unfold gust; refine sum_eq_zero fun p _=>?_; ext1 n; unfold spoolB; exact sum_eq_zero fun i hi=> (congr_arg (grant n) braid_no).trans (grant_zero _) -- adjust
end book
section port
-- Normalized per-slot post exteriors on t=univ. each configuration. EXP Ward cost later.
variable {F:Layouts I G D R}{V:I→BoardU D R G}
def chirpR (X:Chain)(m k:ℕ)(φ:I→Profile D)(R:ℝ)(x:E4)(z:I→Cover) (i:I): Sight D R:= sheet D R (exteriorP (φ i).val (spanP X m k) x (z i))
abbrev cope (X:Chain)(m k:ℕ)(φ:I→Profile D)(x:E4)(R:ℝ) : Finset (I → Cover) := Fintype.piFinset fun i=>blush (φ i) X m k x R
lemma crumbs (X:Chain)(m k:ℕ)(φ:I→Profile D)(x:E4)(R:ℝ)(p:I→Cover)(h:p∉cope X m k φ x R) : ∃ i:I, chirpR X m k φ R x p i=0:= by
    have hp : ¬∀ i,p i∈blush (φ i) X m k x R:= mt Fintype.mem_piFinset.mpr h; push Not at hp; obtain ⟨i,hi⟩:=hp
    refine ⟨i,?_⟩; have hh (b:Sheet D)(t : Scores.Close R): (chirpR X m k φ R x p i).val b t=0:= no_exam (mt blush_v.mpr hi) (Scores.utter D R t b)
    exact Subtype.ext (funext fun b=>ContinuousMap.ext fun t=> hh b t)
def lone (X:Chain)(m k:ℕ)(b:I→ℕ): ℝ:= ∏ i:I,Plot.tariff (b i) (spanP X m k)
def songPX (X:Chain)(F:Layouts I G D R)(b:I→ℕ)(p:I→ Profile D)(m k:ℕ)(x:E4)(z:I→Cover): Tale G := lone X m k b • SolarPaper F z (chirpR X m k p R x z) univ
def sang (X:Chain)(F:Layouts I G D R)(b:I→ℕ)(p:I→ Profile D)(m k:ℕ)(x:E4): Tale G := ∑ z∈cope X m k p x R,songPX X F b p m k x z
lemma song_t (X:Chain)(p:I→ Profile D)(h:Sense a F)(b:I→ℕ)(m k:ℕ)(x:E4)(z:I→Cover): Stone (vanes a univ) (songPX X F b p m k x z):= (stone_p (h.stone _ _) univ).weight _
lemma song_slice (X:Chain)(p:I→ Profile D)(F:Layouts I G D R)(z:I→ Cover)(x:E4)(h:z∉cope X m k p x R)(b:I→ℕ): songPX X F b p m k x z=0:= by
   obtain ⟨i,hi⟩:= crumbs X m k p x R z h; exact Eq.trans (congr_arg (lone X .. • ·) (slight F z _ i hi univ (mem_univ i))) (smul_zero _)
lemma sings_up (V:I→ℕ→ BoardU D R G)(v:List I)(p:I→Profile D)(x:E4)(hv:v.Nodup)(he:v.toFinset=univ)(h:∀ j,Marvel (a j) (V j i)) (F:I→ℕ): sang X (markZ (fun j=>V j i)) F p m i x = marchFull X m x v F p V i:= by
   let w:= spanP X m i; let k(j:I)(z:Cover):=stemU X (F j) m i (p j).val x (V j i) z
   unfold sang marchFull marchFi Plot.collect
   have hP j z: Stone (a j) (k j z):= (charge_t (p j|>.val) x _ _ (h j) (F j) X z).transport _
   rw [pact_product _ _ hP hv (fun i=>List.mem_toFinset.mp (by rw [he]; simp))]; apply sum_congr rfl; intro z _
   let U j:= V j i; let f(j):= exteriorP (p j).val w x (z j); let b:= chirpR X m i p R x z
   have ht j: Wax.access b (markZ U z) {j} = Town.season (z j) (ringU (f j) (U j)):=eye_sh _ _ _ _ rfl
   unfold songPX lone; rw [←he,hard_p v U z b h hv, show (fun j=>Wax.access b (markZ U z) {j})=fun j=> Town.season (z j) (ringU (f j) (U j)) from funext ht]
   symm
   exact cs_units (a:=a) (F:=fun i=> tariff (F i) w) (h:=fun j _=> (Stone.graph (h j) _).transport (z j)) hv
lemma lone_step (X:Chain)(m k:ℕ)(b:I→ℕ): lone X m (k+1) b=lone X m k b *∏ i,vaneW X b k i:=by
   unfold lone; rw [← prod_mul_distrib]; apply prod_congr rfl; intro i hi; unfold Plot.tariff vaneW rallyW; rw [← spanP_tick X m k, Lattice.site_card]; push_cast; have hz:=spanP_pos X m (k+1); field_simp; ring
lemma spanned_co (z:Places I)(p:I→Profile D)(K:ℕ) (φ:I→Site (X.S.block i))(x:E4)(hp:1/2≤R):
     spar φ (X.S.block_odd i) hp (chirpR X K i p R x z)= chirpR X K (i+1) p R x (footT _ z φ):= by
   funext j; unfold spar chirpR footT; rw [(Pages.scroll_leaf ..).2,retest (spanP_tick X K i|>.symm)]
-- equality read after complete preimage sum
lemma carvedT (X:Chain){P:StripU G (X.S.block i)}(he:Climate P)(hx:1/2≤R)(hp:Sense a F)(p:I→Profile D)(b:I→ℕ)(x:E4)(z:I→Cover):
    songPX X (creekT P a (vaneW X b i) F) b p k i x z=inscribed (vanes a univ) P 0 (∑ ψ:subroll (univ:Finset I) (Site (X.S.block i)), songPX X F b p k (i+1) x (footT (X.S.block i) z (enter univ ψ))) := by
   unfold songPX; rw [crest_p he hx hp, ← inscription_sc 0 (lone X k i b) ?_ he.toFair,Finset.smul_sum]; swap; · apply Stone.group; intro j _; apply Stone.weight; exact stone_p (hp.stone _ _) _
   congr 1; refine sum_congr rfl ?_; intro y _; rw [smul_smul, spanned_co z, lone_step]
private lemma foot_in (X:Chain)(k:ℕ): Injective (fun x : (I→Cover)× subroll (univ:Finset I) (Site (X.S.block k))=> footT (X.S.block k) x.1 (enter univ x.2)) := by
    intro x y hx; have hh(i): (x.1 i, enter univ x.2 i)=(y.1 i, enter univ y.2 i):= by
       let L:=X.S.block k; have hp(z: Cover)(p:Site L): (growP L (stemA L z p),growL L (stemA L z p))=(z,p):= Prod.ext (stemA_fit L (z,p)|>.1) (stemA_fit L (z,p)|>.2)
       exact (hp _ _).symm.trans ((congr_arg (fun z=> (growP L z,growL L z)) (congr_fun hx i)).trans (hp _ _))
    refine Prod.ext (funext fun i=>congr_arg Prod.fst (hh i)) (funext fun i=>?_)
    have hv : enter univ x.2 i=enter univ y.2 i:=congr_arg Prod.snd (hh i)
    unfold enter at hv; rw [dif_pos i.property,dif_pos i.property] at hv; exact hv
lemma song_e (X:Chain){P: StripU G (X.S.block i)}(he:Climate P)(hx:1/2≤R)(hp:Sense a F)(p:I→Profile D)(b:I→ℕ)(x:E4):
    sang X (creekT P a (vaneW X b i) F) b p m i x=inscribed (vanes a univ) P 0 (sang X F b p m (i+1) x):=by
    let L:=X.S.block i; let Z:= cope X m i p x R ×ˢ (univ: Finset (subroll (univ:Finset I) (Site L))); let k (z: (I→Cover) × subroll (univ:Finset I) (Site L)):= footT L z.1 (enter univ z.2)
    let f:= songPX X F b p m (i+1) x
    have hk : cope X m (i+1) p x R ⊆ Z.image k:= by
       intro y hy; have hh:= Fintype.mem_piFinset.mp hy
       refine mem_image.mpr ⟨(fun i=> growP L (y i), fun i=> growL L (y i)), mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun i=> blush_v.mpr (descendant hx (blush_v.mp (hh i)))), mem_univ _⟩, funext fun i=>?_⟩
       unfold k footT enter; dsimp only; rw [dif_pos (mem_univ i)]; exact grows ..
    unfold sang; rw [Finset.sum_subset hk (fun i _ hi=>song_slice X p F i x hi b), Finset.sum_image (fun _ _ _ _ h=> foot_in _ _ h),Finset.sum_product]
    simp_rw [fun z=> carvedT X he hx hp p b x z (k:=m)]
    exact (inscript_list (cope X m i p x R) _ _ (fun i h=> Stone.group univ (fun r: subroll (univ:Finset I) (Site L)=> f (footT L i (enter univ r))) (fun k _=> song_t _ _ hp _ _ _ _ _)) he.toFair).symm
end port
end YM.RG08.Creek
