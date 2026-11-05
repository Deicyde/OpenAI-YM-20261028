import YM.RG08.Creek.Kinks
/-! # Singleton packet formula with commuting gust. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door Analysis
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Wings High Pill Taste Run Matrix PowerSeries
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I:Type}[Fintype I][DecidableEq I]{G:Gauge}{i j k D:ℕ}{R:ℝ}{a:I→ℕ}{T:Finset I}
private lemma bill_l {X:Type}(h g f:ℕ→Psalm X) (i:ℕ) : billow (billow h g) f i=billow h (billow g f) i:= by
    funext p; let V(Y:ℕ→Psalm X) : PowerSeries ℝ:= PowerSeries.mk fun i=> Y i p
    have he (h g:ℕ→Psalm X): V (billow h g)=V h*V g:= by
       ext1 i; unfold V; rw [coeff_mul,coeff_mk]; unfold billow; simp only [Finset.sum_apply,Pi.mul_apply, PowerSeries.coeff_mk]
    have hv : V (billow (billow h g) f)= V (billow h (billow g f)):= by rw [he,he,he,he,mul_assoc]
    have hz:=congr_arg (PowerSeries.coeff i) hv; unfold V at hz; simp only [coeff_mk] at hz; exact hz
lemma gust_asc {F V W:Tale G}(h:Stone i F)(he:Stone j V)(hx:Stone k W): gust (gust F V) W= gust F (gust V W):=by
    have ha:= sails_from h; have hb:= sails_from he; have hc:= sails_from hx
    refine unrolled (sails_from (wind (wind h he) hx)) (by rw [Nat.add_assoc]; exact sails_from (wind h (wind he hx))) (fun i' m=>?_)
    rw [sing_k (braid_s ha hb) hc, Nat.add_assoc i j k,sing_k ha (braid_s hb hc)]; simp_rw [sing_k ha hb,sing_k hb hc]; exact bill_l ..
lemma cast_perm {F:I→Tale G}(h:∀ i,Stone (a i) (F i))(p q:List I)(hp:p.Perm q): castF F p=castF F q:= by
    induction hp with
    | nil=>rfl
    | cons _ _ ih=> exact congr_arg (gust _) ih
    | swap x y l=> change gust (F y) (gust (F x) (castF F l))=gust (F x) (gust (F y) (castF F l)); have hp:Stone (loadᵣ a l) (castF F l):= stone_cast fun i _=>h i; rw [←gust_asc (h y) (h x) hp, ←gust_asc (h x) (h y) hp, gust_same (h x) (h y)]
    | trans _ _ ih hP => exact ih.trans hP
lemma cs_units {t:List I}{P:I→Tale G}(h:∀ i∈t,Stone (a i) (P i))(F:I→ℝ)(hz:t.Nodup): castF (fun i=> F i•P i) t= (∏ i∈t.toFinset,F i) • castF P t:=by
    induction t with
    | nil=> rw [List.toFinset_nil,prod_empty,one_smul]; rfl
    | cons i t ih=>
       have he j (hp:j∈t):= h j (List.mem_cons_of_mem _ hp); have hh:= List.nodup_cons.mp hz; change gust (F i • _) (castF _ t) = _ • gust (P i) (castF P t)
       rw [ih he hh.2, List.toFinset_cons,prod_insert (fun hp=>hh.1 (List.mem_toFinset.mp hp))]
       have hP:=stone_cast he; have hp:= h i (List.mem_cons_self); rw [swell_w hp (hP.weight _),gust_same hp (hP.weight _),swell_w hP hp,gust_same hP hp,smul_smul]
private lemma cast_defs {U:Topaz I (Tale G)}(h:∀ t,Stone (vanes a t) (U t))(he:∀ t,t.card≠1→U t=0)(t:Finset I) : Fabrics G U t=castF (fun i:I=>U {i}) t.toList:=by
   induction t using strongInductionOn with
   | _ t ih =>
    by_cases hz:t=∅; · subst t; change Wax.banner _ _ _ _=_; rw [banner_one]; simp; rfl -- simp nil
    let A:= (partners t).filter (fun i=> i.1.card=1); have hA (p:Finset I×Finset I): p∈A↔ p∈partners t∧p.1.card=1:= mem_filter
    let F (p:Finset I×Finset I):= gust (sons U p.1) (Fabrics G U p.2)
    have hx : (∑ p∈A,F p)=∑ p∈partners t,F p:= sum_subset (filter_subset ..) fun p hp hu=> by unfold F sons; rw [he _ (fun h=>hu ((hA p).mpr ⟨hp,h⟩)),smul_zero, gust_z]
    let K(i:I): Finset I × Finset I := ({i},t.erase i)
    have hv(p)(hp:p∈A): (∃ i∈t,p=K i):= by
       obtain ⟨hh,ht⟩:= (hA p).mp hp; obtain ⟨he,hV⟩:= (norms_par ..).mp hh; obtain ⟨i,hi⟩:= card_eq_one.mp ht; refine ⟨i,?_,Prod.ext hi ?_⟩
       · simp [he,hi]
       change p.2=t.erase i; have hk:i∉ p.2:= Finset.disjoint_left.mp hV (show i∈p.1 by simp [hi]); rw [he, hi]; simp [hk]
    have hk i (hi:i∈t): K i∈ A:= by rw [hA,norms_par]; dsimp only [K]; simp [Finset.insert_erase hi]
    have hK : A=t.image K:= Finset.ext (fun p=> ⟨fun hp=>by obtain ⟨i,hi,hp'⟩:= hv p hp; exact mem_image.mpr ⟨i,hi,hp'.symm⟩, fun hp=>by obtain ⟨i,hi,rfl⟩:= mem_image.mp hp; exact hk _ hi⟩)
    let v(i:I):= U {i}; let g:=castF v t.toList
    have hu i (hi:i∈t): F (K i)=g:= by
       change gust (sons U {i}) (Fabrics G U (t.erase i))=g; rw [sons,card_singleton,Nat.cast_one,one_smul, ih _ (erase_ssubset hi)]
       apply cast_perm (a:=a) ?_ (i::(t.erase i).toList) t.toList; swap; · intro k; have hp:=h ({k}:Finset I); simpa only [vanes, sum_singleton] using hp
       apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr (show i∉ (t.erase i).toList ∧ (t.erase i).toList.Nodup from  ⟨by simp,nodup_toList _⟩)) (nodup_toList _); simp [Finset.insert_erase hi]
    have hB := congr_fun (bannerC (spine_one (Loc G 1)) U gust gust_z (he _ (by simp))|>.2.2) t
    apply smul_right_injective (Tale G) (show (↑t.card:ℝ)≠0 from Nat.cast_ne_zero.mpr (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hz))); change sons (Fabrics G U) t= (↑t.card:ℝ)•g
    rw [show sons _ t=∑ p∈partners t,F p from hB,← hx,hK,Finset.sum_image (fun i _ j _ hp=> singleton_inj.mp (show _ from congr_arg Prod.fst hp))]; rw [Finset.sum_congr rfl (fun i hi=> hu i hi),Finset.sum_const,Nat.cast_smul_eq_nsmul]
-- The product through exponential transmits through all orders.
theorem hard_p (p:List I)(U:I→BoardU D R G)(x:Places I)(b:I→Sight D R)(h:∀ i,Marvel (a i) (U i))(hv:p.Nodup): SolarPaper (markZ U) x b p.toFinset=castF (fun i=> access b (markZ U x) ({i}:Finset I)) p:=by
    have ht:=eyeSense h; rw [SolarPaper,cast_defs (ht.stone x b) (fun i hi=>?_)]
    · apply cast_perm (a:=a) ?_ _ _ ?_; exact fun i=> (by simpa only [vanes,sum_singleton] using ht.stone x b {i})
      apply List.perm_of_nodup_nodup_toFinset_eq (nodup_toList _) hv; simp
    funext h k x'; simp only [Wax.access,markZ,dif_neg hi,Pi.zero_apply,Function.comp_apply,map_zero]
end YM.RG08.Creek
