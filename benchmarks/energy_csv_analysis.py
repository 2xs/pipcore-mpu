#!/usr/bin/env python3
"""
/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
/*  Copyright (C) 2020-2022 Orange                                             */
/*                                                                             */
/*  This software is a computer program whose purpose is to run a minimal,     */
/*  hypervisor relying on proven properties such as memory isolation.          */
/*                                                                             */
/*  This software is governed by the CeCILL license under French law and       */
/*  abiding by the rules of distribution of free software.  You can  use,      */
/*  modify and/ or redistribute the software under the terms of the CeCILL     */
/*  license as circulated by CEA, CNRS and INRIA at the following URL          */
/*  "http://www.cecill.info".                                                  */
/*                                                                             */
/*  As a counterpart to the access to the source code and  rights to copy,     */
/*  modify and redistribute granted by the license, users are provided only    */
/*  with a limited warranty  and the software's author,  the holder of the     */
/*  economic rights,  and the successive licensors  have only  limited         */
/*  liability.                                                                 */
/*                                                                             */
/*  In this respect, the user's attention is drawn to the risks associated     */
/*  with loading,  using,  modifying and/or developing or reproducing the      */
/*  software by the user in light of its specific status of free software,     */
/*  that may mean  that it is complicated to manipulate,  and  that  also      */
/*  therefore means  that it is reserved for developers  and  experienced      */
/*  professionals having in-depth computer knowledge. Users are therefore      */
/*  encouraged to load and test the software's suitability as regards their    */
/*  requirements in conditions enabling the security of their systems and/or   */
/*  data to be ensured and,  more generally, to use and operate it in the      */
/*  same conditions as regards security.                                       */
/*                                                                             */
/*  The fact that you are presently reading this means that you have had       */
/*  knowledge of the CeCILL license and that you accept its terms.             */
/*******************************************************************************/
"""

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import argparse
import sys

parser = argparse.ArgumentParser()
parser.add_argument('file',nargs='+')
args = parser.parse_args()

for filename in args.file:
  #print(filename)

  df = pd.read_csv(filename,
          skiprows=0,
          sep=',',
          header=0,
        )

  #print(df)

  # Find the benchmark test phase by looking for huge power difference because of the processor sleeps
  testphases = []
  df['diffcurrent'] = df['Current (uA)'] - df['Current (uA)'].shift(1) # dataframe of the difference between one period

  testphases = df.index[abs(df['diffcurrent']) > 2000].tolist()
  #print(testphases)


  # remove close points
  testphases_filtered = []
  for timestp in testphases:
    # if new list is empty or distance between the new points and the last inserted is too small
    if not testphases_filtered or abs(timestp - testphases_filtered[-1]) >= 10:
        testphases_filtered.append(timestp)

  #plt.plot(df['Current (uA)'])
  #plt.plot(df.iloc[testphases_filtered]['Current (uA)'], marker='o', markersize=3, color="red")

  # The second and the third markers are the test phase start and end
  # remove the first and last points if extrema too avoid overshoot
  update_first = True
  update_last = True
  update = False # witness an extrema for the last point, laucnhing the whole analysis again
  i = 0
  while update_last:
    i = i + 1
    point_max = df.iloc[testphases_filtered[1]:testphases_filtered[2]]['Current (uA)'].max()
    point_min = df.iloc[testphases_filtered[1]:testphases_filtered[2]]['Current (uA)'].min()
    if update_first:
        point = df.iloc[testphases_filtered[1]]['Current (uA)']
        if (point == point_max or point == point_min):
          # first point is extrema, remove it
          testphases_filtered[1] = testphases_filtered[1] + 1
        else:
          # first point is no extrema anymore, continue with second point
          update_first = False
    else:
        update_last = False
        # first point is no extrema anymore, remove last point if extrema
        point = df.iloc[testphases_filtered[2]]['Current (uA)']
        if point == point_max or point == point_min:
          # last point is extrema, remove it
          testphases_filtered[2] = testphases_filtered[2] - 1
          update_last = True
          update = True
        else:
          # if the last point was an extrema and was removed, check again first point
          if update:
            update_first = True

  #print("Checked %s points" % str(i))

  df_test = df.iloc[testphases_filtered[1]:testphases_filtered[2]].copy() # Slice the data frame to fit the testphase only
  #plt.plot(df_test['Current (uA)'], 'g')

  #plt.show()

  duration = df_test.iloc[-1]['Timestamp (us)'] - df_test.iloc[0]['Timestamp (us)']
  duration /= 1000000 # us -> sec
  df_test['difftime'] = df_test['Timestamp (us)'] - df_test['Timestamp (us)'].shift(1) # dataframe of the difference between one period


  df_test['power'] = df_test['Current (uA)']*3 # fixed 3V voltage by coin cell battery
  df_test['power'] /= 1000 # W -> mW
  df_test['energy'] = df_test['difftime']/1000000*df_test['power'] # dataframe of enery during a period (mWs)

  #plt.plot(df_test['energy'], 'r')
  #plt.show()

  minpower = np.min(df_test['power'])
  maxpower = np.max(df_test['power'])
  mincurrent = np.min(df_test['Current (uA)'])
  maxcurrent = np.max(df_test['Current (uA)'])

  print("Total test duration: %.2f s" % duration)
  print("Average current: %f uA" % df_test['Current (uA)'].mean())
  print("Max current: %f uA" % df_test['Current (uA)'].max())
  print("Min current: %f uA" % df_test['Current (uA)'].min())
  print("Std current: %f uA" % df_test['Current (uA)'].std())
  print("Average power: %f mW" % df_test['power'].mean())
  print("Total energy consumption: %f mWs (mJ)"%df_test['energy'].sum()) # mJ -> energy = integral of the power consumption over the time needed
  #print("Total current consumption: %i uA"%df_test['Current (uA)'].sum())
  #print(df_test.describe())


  # Estimated battery life assuming a 70% efficiency
  # Battery life = ( (300mAh * 3V) / 14.1uW ) * 0.7 = 44681 hrs = 1860 days

  # https://devzone.nordicsemi.com/f/nordic-q-a/17059/help-me-understanding-theorical-power-consumption-of-nrf52832

  # Timer0 uses more current than RTC
  # https://devzone.nordicsemi.com/f/nordic-q-a/74648/understanding-power-consumption

  # Save current
  # https://devzone.nordicsemi.com/guides/short-range-guides/b/hardware-and-layout/posts/nrf51-current-consumption-guide
  # Average current consumption of device: 20 uA
  # Energy capacity: 220 mAh (typical CR2032 coin cell battery)
  # Battery lifetime: 0,22 Ah / 0,00002 A = 11,000 hours = 458 days
  #
  # Current should be measured on battery because USB draxs about 1uA-2uA

  #
  # https://devzone.nordicsemi.com/f/nordic-q-a/431/what-is-the-power-and-clock-model-of-peripheral-in-nrf51
