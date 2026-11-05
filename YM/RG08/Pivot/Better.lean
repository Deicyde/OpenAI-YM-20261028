import YM.RG08.Pivot.Vale

set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis Reflect Finset Needle Source Source.Drops Labels Planned.PrimaryIntegral295
open scoped Topology BigOperators
variable {I E : Type} {L: Side} {G:Gauge} {R c:ℝ} {r d n D t j : ℕ} {F:Frame G d} {S:SectionData F}
variable {V:EnvelopeU D R G r}

lemma boarding_cast {Q:Cross L (Loc G 1) (Loc G 1)}(he:Odd L.val)(hp:1/2≤R)(hx:Whole Q)(V : I→ EnvelopeU D R G r)(A:Finset I)(hv:∀ a∈A,Tidy (V a))(t:ℕ):
    aboard t Q (∑ i∈A,V i)=∑ i∈A,aboard t Q (V i) := by
  classical
  induction A using Finset.induction_on with
  | empty => rw [sum_empty,sum_empty,zero_aboard t he hp hx]
  | insert i S hi IH=>
    have hr j (hj:j∈S):= hv j (mem_insert_of_mem hj)
    rw [sum_insert hi,sum_insert hi, aboard_add he hp hx (hv i (mem_insert_self ..)) (Tidy.additions hr),IH hr]
lemma pokescale {Q:Cross L (Loc G 1) (Loc G 1)}(he:Odd L.val)(hp:1/2≤R)(_ : Whole Q)(x:ℝ) (_:Tidy V):
    aboard t Q (x•V)=x • aboard t Q V := by
  unfold aboard; rw [smul_comm x]; congr 1; rw [Finset.smul_sum]; apply sum_congr rfl; intro i hi
  unfold Vale.halo belly revolve; funext k
  simp only [Shade.readdress,he,hp,true_and,↓reduceDIte,sires,Pi.smul_apply]; rw [← tsum_const_smul'']; refine tsum_congr fun a => ?_; rw [smul_comm x]; congr 1
lemma pax (X:Cross L (TypeFace 1) (TypeFace 1))(he:Odd L.val)(hp:1/2≤R)(hx:Whole X)(h:Toute V): Toute (aboard t (painted G X) V) :=
    tot_weight (tot_sums (F:=fun i:Site L=> Vale.halo i V (painted G X)) (fun i _=>paid_color h X hx i he hp)) _
lemma projection_prime (H:Hol G)(Q: Flight j n)(hx:0<c)(hn:4 ≤ n) (hr:d≤ j)(hv:1/2≤R)(hF: Gold V)(hp:Polished V)
    (b:Letter F)(he:slot b=r)(hX:S.Sound H)(hT:Bid.pop S)(ht:d≤D):
    invest H (aboard d (painted G (Carrier.linesOf Q c)) V) b=
      ∑ i∈ (univ:Finset (Letter F)).filter (slot · = slot b), leadingV H S ht hv Q c i b * invest H V i := by
  let g:Hol G:=H; let hR : 0≤R := (by norm_num : (0:ℝ)≤1/2).trans hv
  let F0 (p : Letter F):= startU S p ht hR
  subst r
  let I:= (univ : Finset (Letter F)).filter (slot ·= slot b)
  let X i:= F0 i 0 (slot b)
  let L (i : Letter F):= invest H V i
  let U i:= L i • X i; let A:= ∑ i∈I,U i; let B:=Carrier.linesOf Q c; let Z:=painted G B
  have hw i : Marvel (slot i) (F0 i):= start_duty S i ht hR hT H hX
  have hu i: Gold (X i):= sober_vetted (hw i); have hh i: Polished (X i):= start_lank S i ht hR 0 (slot b)
  have hU : Gold A:= gold_sum (fun i _=> gold_scale (hu i) (L i)); have hA:Polished A := polished_sum (fun i _=>polished_scale (hh i) (L i))
  have hi (i:Letter F) (hp: slot i = slot b): invest H (V-A) i=0:=by
    rw [invest_less H _ ‹_› hA hF.toToute hU.toToute,sub_eq_zero]
    unfold A; rw [invest_sum H i I (fun j _=>(gold_scale (hu j) _).toToute) (fun j _=>polished_scale (hh j) _)]
    have hv b' (hz:slot b'=slot b): invest H (X b') i = if i=b' then 1 else 0 := by
      have hx: ∀ j,slot b=j→ slot i=j → invest H (F0 b' 0 j) i=if i=b' then 1 else 0:= fun j hj hl=> by subst j; rw [← hz]; exact projected b' H hX hT ht hR i (hp.trans hz.symm)
      exact hx _ rfl hp
    rw [sum_eq_single i]; · rw [invest_sm _ _ _ (hu _).toToute (hh _),hv _ hp, if_pos rfl,mul_one]
                             -- refl?
    · intro j hj he; rw [invest_sm _ _ _ (hu _).toToute (hh _),hv _ (mem_filter.mp hj|>.2),if_neg (Ne.symm he),mul_zero]
    exact fun e=> (e (mem_filter.mpr ⟨mem_univ _,hp⟩)).elim
  have hx:= idle_push (t:=d) H Q hx hn hr hv (gold_less hF hU) (show Polished (V-A) from (sub_eq_add_neg V A) ▸ polished_more hp (polished_neg hA)) hi b rfl -- arg order
  have hZ:= spray_whole (G:=G) Q c ‹0<c› hn; have hB:= Carrier.stored Q c ‹_› hn
  rw [aboard_sub Q.odd hv hZ hF.toTidy hU.toTidy, invest_less H _ (all_aboard Q.odd hv hZ hp) (all_aboard Q.odd hv hZ hA) (pax B Q.odd hv hB hF.toToute) (pax B Q.odd hv hB hU.toToute),sub_eq_zero] at hx
  rw [hx,show A=_ from (rfl:A=∑ i∈I,U i)]; rw [boarding_cast Q.odd hv hZ U _ (fun i _=>(hu i).toTidy.scale (L i)) d]
  rw [invest_sum H _ I (fun i _=>pax B Q.odd hv hB (gold_scale (hu i) (L i)|>.toToute)) (fun i _=>all_aboard Q.odd hv hZ (polished_scale (hh i) (L i)))]
  apply Finset.sum_congr rfl; intro i hi
  rw [pokescale Q.odd hv hZ _ (hu i).toTidy,invest_sm _ _ _ (pax B Q.odd hv hB (hu i).toToute) (all_aboard Q.odd hv hZ (hh i)),mul_comm (L i)]
  have hr:= mem_filter.mp hi|>.2
  have heq : invest H (aboard d Z (X i)) b=leadingV H S ht hv Q c i b:= by unfold X; rw [← hr]; rfl
  rw [show invest H (aboard d _ (X i)) b=_ from heq]
end YM.RG08.Pivot
