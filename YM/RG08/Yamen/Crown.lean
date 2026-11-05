import YM.RG08.Yamen.Station

/-! # Wilson boot every e. -/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason Supplies Flat Filter
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{a:Levels G}{F:Horizon a}{P X:MapPrices}

def top (G:Gauge):Castle G:= fun r e=>if e=r∧Even e then Crown.prize G (RG08.Mount.rank r) else 0
local notation "o"=>RG08.Mount.stick 0
lemma festival {N:ℕ}(hF:F.Suffices P): Seed (F.H N N) (Crown.prize G 2):=by
 obtain ⟨p,hp,hU⟩:= Crown.earned (σ:=1) G 2 o
 let Y:=Crown.prize G 2;let H:=picture G.ColorIndex 2 Y
 have ht:Cloak (Symmetry.dressed G 2) 2 Y:=Crown.home _ (by decide) o
 let B:= F.H N N
 have hx := (hF.rows N N le_rfl).2.1
 let s:=min 1 (P.α (a.clock.J N));have hs:0<s:=lt_min (by positivity) (P.alpha_pos _)
 let t:=P.Ω (a.clock.J N);have hb:t≥0:=Ω_pos hF N
 obtain ⟨h1,h2⟩:=output_cost (Y:=B) (σ:=s) (fun i j=> (hx i j).mono (min_le_right ..) le_rfl) hb hs.le (min_le_left ..)
 -- hroot cohort & held via spur_cost.
 have he: Cohort (Cast.root G B) := Anchor.expand_path (Cast.spur_path (G:=G) (D:=Flat.output B) (Cast.light_cities _)) -- check args
 let r:= Flat.sumToken*(Fintype.card Faces*t);have hr:0≤r:=mul_nonneg Flat.sumToken_pos (mul_nonneg (Nat.cast_nonneg _) hb)
 have hR:Held (carpet _) s (Cast.tax G 1 *r) (Cast.root G B):=Anchor.expand_cost (Cast.spur_cost h1 (Cell.col_of_row ?help h1) hr hs.le)
 case help=> exact Cast.light_cities _
 have hp':0 ≤ p:=zero_le_one.trans hp
 obtain ⟨hf,hM⟩: Graded H 1 ∧ Held (carpet _) ((1:ℝ)/2) (flashes G.ColorIndex 2 1*p) H:=⟨(Cast.bearing (ht.field')).2,encode (Fin.pos o) zero_lt_one hp' ht.path hU⟩
 let D:= (1/2:ℝ) • Cast.root G B
 have hg : Graded D 1 := by apply graded_iff.mpr;intro i x he;change (1/2:ℝ) • Cast.root G B x=0; rw [(graded_iff (F:=Cast.root G B)).mp (by apply Anchor.expand_grade) _ _ he,smul_zero] -- rfl? lemma
 have hQ:=hR.smul (1/2:ℝ)
 refine ⟨⟨ht,1,p,zero_lt_one,hp',hU⟩,?_,Crown.core_top _⟩
 apply Cast.compress_inj _ _ hf hg
 have hQ0(P:Side):pour (P:=P) (compress 1 H) o=pour (compress 1 D) o:=by
   rw [←Carrel.complete_top _ o ht hU hp' zero_lt_one,show pour (P:=P) (completed Y o 2) o=_ from Crown.basement G P,show pour (compress 1 D) o=(1/2:ℝ) • (pour (P:=P) (compress 1 (Cast.root G B)) o) from by
          ext x;rw [Pi.smul_apply,pour_at,pour_at];change (∑' z: lantern o x,(1/2:ℝ)*compress 1 (Cast.root G B) z.val)=_;rw [tsum_mul_left];rfl,Cast.root,Cast.beam, show compress 1 (Anchor.extend 1 (Cast.spur G _))=Cast.spur G (Flat.output B) from funext (fun i=>Anchor.extend_top ..),show pour (P:=P) (Cast.spur G (Flat.output B)) o=_ from Cast.spur_matches (h2 P),show quadratic B P=Precision.K 1 from same_terminal hF N P]
 ext x
 have hHH:= (Spar.photograph (NextTo.unit zero_lt_one hp' ht.path hU (Fin.pos o))).cohort
 have hP:= Spar.cofinal (K:=compress 1 H) (Anchor.compress_path 1 hHH) (θ:=(1:ℝ)/2) (C:=flashes G.ColorIndex 2 1*p) (by positivity) (by have he:=flame_pos (I:=G.ColorIndex) (n:=2) (show (0:ℝ)<1 by positivity) (by omega);positivity) (Anchor.compress_cost _ hM) o (l:=chain) Isles.rise x
 simp_rw [hQ0] at hP
 exact tendsto_nhds_unique hP (Spar.cofinal (Anchor.compress_path 1 (he.smul (1/2:ℝ))) _ _ hs (by exact mul_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hr)) (Anchor.compress_cost _ hQ) o Isles.rise x)

lemma trial(N:ℕ)(hF:F.Suffices P) : Tires (F.H N N) (Yamen.top G):=by
 constructor
 · refine ⟨fun r i he=>?_,?_⟩
   · unfold top;rw [if_neg (by rintro ⟨rfl,x⟩;exact he ⟨le_rfl,_,rfl⟩)]
   intro r e;unfold top;split
   next ht=>
     obtain ⟨p,hp,h⟩:= Crown.earned (σ:=1) G (RG08.Mount.rank r) (RG08.Mount.stick r)
     exact ⟨Crown.home (RG08.Mount.rank r) (by obtain ⟨h,q,h'⟩:=ht; unfold RG08.Mount.rank; exact ⟨q+1,by omega⟩) (RG08.Mount.stick r),1,p,zero_lt_one,zero_le_one.trans hp,h⟩
   next=>exact Honor.nil
 · unfold top;rw [if_pos ⟨rfl,Even.zero⟩];exact festival hF
 intro e he
 unfold top;rw [if_neg (fun h=>he h.1)]
 intro i j _ _ y;unfold Loop.spectrum Loop.AxisK Loop.load Loop.col hum;dsimp only [Pi.zero_apply];simp
end YM.RG08.Yamen
